module AlefeldPotraShi

import Roots

## {{{ APS

"""

    Roots.a42(f, a, b; kwargs...)

(not exported)

Finds the root of a continuous function within a provided
interval [a, b], without requiring derivatives. It is based on algorithm 4.2
described in: 1. G. E. Alefeld, F. A. Potra, and Y. Shi, "Algorithm 748:
enclosing zeros of continuous functions," ACM Trans. Math. Softw. 21,
327–344 (1995).


input:
    `f`: function to find the root of
    `a`, `b`: the initial bracket, with: a < b, f(a)*f(b) < 0
    `xtol`: acceptable error (it's safe to set zero for machine precision)
    `maxeval`:  maximum number of iterations

output:
    an estimate of the zero of f

By John Travers

"""
function a42(f, a, b;
      xtol=zero(float(a)),
      maxeval::Int=15,
      verbose::Bool=false)
    if a > b
        a,b = b,a
    end
    fa, fb = f(a), f(b)

    if a >= b || sign(fa)*sign(fb) >= 0
        error("on input a < b and f(a)f(b) < 0 must both hold")
    end
    if xtol < 0.0
        error("tolerance must be >= 0.0")
    end

    c, fc = secant(f, a, fa, b, fb)
    a42a(f, a, fa, b, fb, c, fc,
         xtol=xtol, maxeval=maxeval, verbose=verbose)
end

"""

Split Alefeld, F. A. Potra, and Y. Shi algorithm 4.2 into a function
where `c` is passed in.

Solve f(x) = 0 over bracketing interval [a,b] starting at c, with a < c < b

"""
a42a(f, a, b, c; args...) = a42(f, a, f(a), b, f(b), c, f(c); args...)

function a42a(f, a, fa, b, fb, c, fc;
       xtol=zero(float(a)),
       maxeval::Int=15,
       verbose::Bool=false)

    try
        # re-bracket and check termination
        a, fa, b, fb, d, fd = bracket(f, a, fa, b, fb, c, fc, xtol)
        ee, fee = d, fd
        for n = 2:maxeval
            # use either a cubic (if possible) or quadratic interpolation
            if n > 2 && distinct(f, a, fa, b, fb, d, fd, ee, fee)
                c, fc = ipzero(f, a, fa, b, fb, d, fd, ee, fee)
            else
                c, fc = newton_quadratic(f, a, fa, b, fb, d, fd, 2)
            end
            # re-bracket and check termination
            ab, fab, bb, fbb, db, fdb = bracket(f, a, fa, b, fb, c, fc, xtol)
            eb, feb = d, fd
            # use another cubic (if possible) or quadratic interpolation
            if distinct(f, ab, fab, bb, fbb, db, fdb, eb, feb)
                cb, fcb = ipzero(f, ab, fab, bb, fbb, db, fdb, eb, feb)
            else
                cb, fcb = newton_quadratic(f, ab, fab, bb, fbb, db, fdb, 3)
            end
            # re-bracket and check termination
            ab, fab, bb, fbb, db, fdb = bracket(f, ab, fab, bb, fbb, cb, fcb, xtol)
            # double length secant step; if we fail, use bisection
            if abs(fab) < abs(fbb)
                u, fu = ab, fab
            else
                u, fu = bb, fbb
            end
            # u = abs(fab) < abs(fbb) ? ab : bb
            cb = u - 2*fu/(fbb - fab)*(bb - ab)
            fcb = f(cb)
            if abs(cb - u) > (bb - ab)/2
                ch, fch = ab+(bb-ab)/2, f(ab+(bb-ab)/2)
            else
                ch, fch = cb, fcb
            end
            # ch = abs(cb - u) > (bb - ab)/2 ? ab + (bb - ab)/2 : cb
            # re-bracket and check termination
            ah, fah, bh, fbh, dh, fdh = bracket(f, ab, fab, bb, fbb, ch, fch, xtol)
            # if not converging fast enough bracket again on a bisection
            if bh - ah < 0.5*(b - a)
                a, fa = ah, fah
                b, fb = bh, fbh
                d, fd = dh, fdh
                ee, fee = db, fdb
            else
                ee, fee = dh, fdh
                a, fa, b, fb, d, fd = bracket(f, ah, fah, bh, fbh, ah + (bh - ah)/2, f(ah+(bh-ah)/2), xtol)
            end

            verbose && println(@sprintf("a=%18.15f, n=%s", float(a), n))

            if nextfloat(ch) * prevfloat(ch) <= 0
                throw(Roots.StateConverged(ch))
            end
            if nextfloat(a) >= b
                throw(Roots.StateConverged(a))
            end
        end
        throw(Roots.ConvergenceFailed("More than $maxeval iterations before convergence"))
    catch ex
        if isa(ex, Roots.StateConverged)
            return ex.x0
        else
            rethrow(ex)
        end
    end
    throw(Roots.ConvergenceFailed("More than $maxeval iterations before convergence"))
end



# calculate a scaled tolerance
# based on algorithm on page 340 of [1]
function tole{S,R}(a::S, b::R, fa, fb, tol)
    T = promote_type(S,R)
    u = abs(fa) < abs(fb) ? abs(a) : abs(b)
    2u*eps(T) + tol
end


# bracket the root
# inputs:
#     - f: the function
#     - a, b: the current bracket with a < b, f(a)f(b) < 0
#     - c within (a,b): current best guess of the root
#     - tol: desired accuracy
#
# if root is not yet found, return
#     ab, bb, d
# with:
#     - [ab, bb] a new interval within [a, b] with f(ab)f(bb) < 0
#     - d a point not inside [ab, bb]; if d < ab, then f(ab)f(d) > 0,
#       and f(d)f(bb) > 0 otherwise
#
# if the root is found, throws a StateConverged instance with x0 set to the
# root.
#
# based on algorithm on page 341 of [1]
function bracket(f, a, fa, b, fb, c, fc, tol)
    # @assert fa == f(a)
    # @assert fb == f(b)
    # @assert fc == f(c)
    if !(a <= c <= b)
        error("c must be in (a,b)")
    end
    delta = 0.7*tole(a, b, fa, fb, tol)
    if b - a <= 4delta
        c = (a + b)/2
        fc = f(c)
    elseif c <= a + 2delta
        c = a + 2delta
        fc = f(c)
    elseif c >= b - 2delta
        c = b - 2delta
        fc = f(c)
    end
    if fc == 0
        throw(Roots.StateConverged(c))
    elseif sign(fa)*sign(fc) < 0
        aa, faa = a, fa
        bb, fbb = c, fc
        db, fdb = b, fb
    else
        aa, faa = c, fc
        bb, fbb = b, fb
        db, fdb = a, fa
    end
    if bb - aa < 2*tole(aa, bb, faa, fbb, tol)
        x0 = abs(faa) < abs(fbb) ? aa : bb
        throw(Roots.StateConverged(x0))
    end
    aa, faa, bb, fbb, db, fdb
end


# take a secant step, if the resulting guess is very close to a or b, then
# use bisection instead
function secant{T}(f, a::T, fa, b, fb)
    # @assert fa == f(a)
    # @assert fb == f(b)
    c = a - fa/(fb - fa)*(b - a)
    tol = eps(T)*5
    if isnan(c) || c <= a + abs(a)*tol || c >= b - abs(b)*tol
        return a + (b - a)/2, f(a+(b-a)/2)
    end
    return c, f(c)
end


# approximate zero of f using quadratic interpolation
# if the new guess is outside [a, b] we use a secant step instead
# based on algorithm on page 330 of [1]
function newton_quadratic(f, a, fa, b, fb, d, fd, k::Int)
    # @assert fa == f(a)
    # @assert fb == f(b)
    # @assert fd == f(d)
    B = (fb - fa)/(b - a)
    A = ((fd - fb)/(d - b) - B)/(d - a)
    if A == 0
        return secant(f, a, fa, b, fb)
    end
    r = A*fa > 0 ? a : b
    for i = 1:k
        r -= (fa + (B + A*(r - b))*(r - a))/(B + A*(2*r - a - b))
    end
    if isnan(r) || (r <= a || r >= b)
        r, fr = secant(f, a, fa, b, fb)
    else
        fr = f(r)
    end
    return r, fr
end


# approximate zero of f using inverse cubic interpolation
# if the new guess is outside [a, b] we use a quadratic step instead
# based on algorithm on page 333 of [1]
function ipzero(f, a, fa, b, fb, c, fc, d, fd)
    # @assert fa == f(a)
    # @assert fb == f(b)
    # @assert fc == f(c)
    # @assert fd == f(d)
    Q11 = (c - d)*fc/(fd - fc)
    Q21 = (b - c)*fb/(fc - fb)
    Q31 = (a - b)*fa/(fb - fa)
    D21 = (b - c)*fc/(fc - fb)
    D31 = (a - b)*fb/(fb - fa)
    Q22 = (D21 - Q11)*fb/(fd - fb)
    Q32 = (D31 - Q21)*fa/(fc - fa)
    D32 = (D31 - Q21)*fc/(fc - fa)
    Q33 = (D32 - Q22)*fa/(fd - fa)
    c = a + (Q31 + Q32 + Q33)
    fc = f(c)
    if (c <= a) || (c >= b)
        c, fc = newton_quadratic(f, a, fa, b, fb, d, fd, 3)
    end
    return c, fc
end


# floating point comparison function
function almost_equal(x, y)
    # FIXME This should be eps(T), why is this Float64?
    # FIXME Also, realmin is 1e-308, it's too tiny to be useful here.
    const min_diff = realmin(Float64)*32
    abs(x - y) < min_diff
end


# check that all interpolation values are distinct
function distinct(f, a, f1, b, f2, d, f3, e, f4)
    # @assert f1 == f(a)
    # @assert f2 == f(b)
    # @assert f3 == f(d)
    # @assert f4 == f(e)
    !(almost_equal(f1, f2) || almost_equal(f1, f3) || almost_equal(f1, f4) ||
      almost_equal(f2, f3) || almost_equal(f2, f4) || almost_equal(f3, f4))
end

## }}}

end
