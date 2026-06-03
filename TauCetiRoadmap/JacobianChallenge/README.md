# Roadmap: the Jacobian challenge (Christian Merten's AG version)

Background: Kevin Buzzard's "Jacobian challenge" (Zulip
[#Autoformalization > Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/583336-Autoformalization/topic/Jacobian.20challenge)),
in the **algebraic-geometry formulation due to Christian Merten**. The challenge is
designed with **checks along the way**, so a construction that satisfies them all has to
have the definitions right; the point is autoformalizing *definitions*, not just
discharging `sorry`s.

**We are not waiting for Mathlib.** The prerequisite stack (scheme-theoretic divisors,
relative coherent cohomology and base change, the Picard functor, abelian varieties) is
mostly absent and will not arrive on a schedule we can plan around. So this is a roadmap
to **build the whole tower here**, in `TauCeti/`, iteratively. Suggested home:
`TauCeti/AlgebraicGeometry/Jacobian/`, with supporting theories under
`TauCeti/AlgebraicGeometry/` (divisors, cohomology, Picard, curves, abelian varieties).

> ⚠ **Name clash.** Mathlib's `WeierstrassCurve.Jacobian` / `EllipticCurve/Jacobian`
> means **Jacobian *coordinates*** (a projective chart `[X : Y : Z]`), *unrelated* to the
> **Jacobian *variety*** built here. Use a name like `JacobianVariety` to avoid it.

## The end goal (v1)

For a **smooth, proper, geometrically connected curve `X` over a field `k` with a
`k`-rational point `x₀`**, construct the **Jacobian** `Jac X = Pic⁰(X)` as an abelian
variety over `k`, characterized by the universal property of the Abel–Jacobi map and
compatible with base change.

```lean
-- the shape we are building toward (state in Targets.lean as the types appear):
-- noncomputable def JacobianVariety (X : Curve k) (x₀ : X.RationalPoint) : AbelianVariety k
-- def abelJacobi : X ⟶ (JacobianVariety X x₀).toScheme            -- x₀ ↦ 0
-- -- universal property: for every abelian variety A and pointed morphism f : (X,x₀) → (A,0),
-- -- there is a unique homomorphism φ : Jac X → A of abelian varieties with f = φ ∘ aj.
-- theorem jacobian_baseChange (K) [Field K] [Algebra k K] :
--     (JacobianVariety X x₀).baseChange K ≅ JacobianVariety (X.baseChange K) (x₀.baseChange K)
```

In the AG version, comparison of independently-built solutions is *automatic*: the
universal property supplies the isomorphism (Christian Merten).

## Standing hypotheses (spell them out; never bake in)

`X` smooth + proper + geometrically connected of dimension 1 over a field `k`; record as a
lemma that such a curve is **geometrically integral** (smoothness ⇒ geometric reducedness;
regular + connected ⇒ irreducible). A chosen `k`-rational point `x₀`. The Jacobian scheme
`Pic⁰` is representable for such curves over a field **without** a `k`-point; the `k`-point
*rigidifies/normalizes* the Picard functor and supplies the Abel–Jacobi morphism.

## Inventory: what Mathlib master gives us (consume)

- **Morphism properties**, `Mathlib/AlgebraicGeometry/Morphisms/*`: `Proper`, `Smooth`,
  `Separated`, `Flat`, `FiniteType`, `FinitePresentation`, `ClosedImmersion`, `Etale`, …,
  every adjective for "smooth proper curve", plus the flat/proper/fp hypotheses the
  relative theory needs.
- **Geometric conditions**: `Mathlib/AlgebraicGeometry/Geometrically/{Connected,Integral}.lean`.
- **Affine Picard / class groups**: `Mathlib/RingTheory/PicardGroup.lean` (`CommRing.Pic`)
  and `ClassGroup.equivPic`. Useful *algebraic ingredients for affine charts*; they are
  **not** a direct foundation for the global Picard scheme (the work is invertible sheaves
  as locally free sheaves, gluing, and descent).
- **General sheaf cohomology on a site**: `Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean`,
  `Mathlib/AlgebraicGeometry/Sites/BigZariski.lean`. ⚠ Abstract only: **coherent-sheaf
  cohomology of schemes** (finiteness, base change, the curve's `H⁰/H¹`) is **not** here
  (Layers B–C).
- **Rigidity**, `Mathlib/AlgebraicGeometry/Group/Abelian.lean`: a proper group scheme is
  commutative. Use it for general abelian-variety API; note `Pic⁰` is commutative *directly*
  (tensor product of line bundles), so rigidity is not needed for that.
- **`Proj` / projective space**: `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/*`.
- **Genus-1 ingredients**, `Mathlib/AlgebraicGeometry/EllipticCurve/*`: the group law on
  the points of an elliptic curve is built in `EllipticCurve/Affine/Point.lean` **through
  the class group** (`ClassGroup.mk W.FunctionField (XYIdeal' …)`), i.e. the divisor-class /
  `Pic⁰` description in genus 1. This is a **reconciliation target and a template**, *not*
  a scheme-level `Jac(E) ≅ E`; that statement still has to be built.

## Inventory: what is missing (build here)

Scheme-theoretic Weil/Cartier **divisors** and the divisor ↔ line-bundle dictionary; the
**degree** map and **Pic⁰**; **coherent-sheaf cohomology** with **finiteness, Serre
duality, Riemann–Roch** over `k`; the **relative** theory, i.e. proper-flat pushforward,
**cohomology and base change / semicontinuity / Grauert**, relative effective Cartier
divisors; the **Picard functor**, its **rigidification** (Poincaré bundle) and
**representability**, and `Pic⁰` with its **properness/projectivity**; **abelian varieties**
(dimension, tangent space, dual, polarizations, the theorem of the cube/square); the
**Abel–Jacobi** morphism, universal property, and base change. The fppf-sheaf /
faithfully-flat-descent lane is a shared prerequisite (also in the reductive-groups roadmap).

---

## The prerequisite tower (build order)

Codex's recommended dependency order, refined. Each layer is self-contained mathematics
worth having on its own. As a layer makes the next one's *types* expressible, state those
milestones in `Targets.lean` (with `sorry`) and hand them to the AIs.

### Layer A, line bundles, divisors, Picard group, degree
- **Invertible sheaves** on a scheme; the **Picard group** `Pic X` under `⊗`.
- **Divisors on a curve:** Weil divisors `⊕_x ℤ` and Cartier divisors; the dictionaries
  `Cartier ≃ line bundles` and (smooth curve) `Weil ≃ Cartier`; principal divisors;
  `Cl(X) ≅ Pic X`.
- **Degree.** Define `deg L := χ(L) − χ(𝒪_X)` (this equals `Σ_x [κ(x):k]·ord_x` for the
  divisor of `L`; prove agreement). ⚠ Note `χ(L) = dim H⁰ − dim H¹` is the *Euler
  characteristic*, **not** the degree. Then `Pic⁰ X = ker deg` (as an abstract group; the
  *functorial* `Pic⁰` is defined in Layer D).

### Layer B, coherent cohomology over `k`: genus, Riemann–Roch, Serre duality
- **Coherent sheaves** and cohomology `Hⁱ(X, ℱ)`: acyclicity of affines, Čech ≃ derived on
  a separated scheme, **finite-dimensionality for proper `X/k`**, vanishing above dimension
  (`H²= 0` on a curve).
- **Genus** `g := dim_k H¹(X, 𝒪_X)`; **Riemann–Roch** `χ(L) = deg L + 1 − g`; **Serre
  duality** with the **relative dualizing sheaf** `ω_{X/k}`: `Hⁱ(L) ≅ H^{1−i}(ω_{X/k} ⊗ L⁻¹)*`
  and `deg ω_{X/k} = 2g − 2`.

### Layer C, relative coherent cohomology and base change
The part that the classical "Sym^g" story quietly relies on, so it comes *before* Picard.
- Proper-flat-finitely-presented pushforward of coherent sheaves; **flat base change**;
  **cohomology and base change / semicontinuity** (Grauert), and the theorem on formal
  functions if following Grothendieck's Picard-scheme proof.
- **Relative effective Cartier divisors** and **symmetric powers** `Symᵈ X` (smooth
  projective for a smooth curve): the geometric input to the Abel maps.

### Layer D, the relative Picard functor and the Jacobian scheme
- **The functor.** For `f : X → Spec k` proper, flat, finitely presented with
  geometrically integral fibres (so `f_*𝒪_X = 𝒪` universally), `Pic_{X/k}` is the **fppf
  sheafification** of `T ↦ Pic(X_T)/Pic(T)`. Keep the three notions distinct (Picard
  *stack* vs *functor/sheaf* vs *rigidified functor*), and record the obstruction
  (`Br`-flavoured) between `Pic(X_T)/Pic(T)` and `Pic_{X/k}(T)`. The section `x₀`
  **rigidifies** it (line bundles trivialized along `x₀,T`; the **Poincaré bundle**) and
  removes that obstruction.
- **`Pic⁰`** = the degree-0 **open-and-closed component** of the relative Picard scheme
  once it exists (before representability: the subfunctor of line bundles of degree 0 on
  every geometric fibre; mind local constancy of degree in flat families).
- **Representability, the crux** (both routes hide heavy infrastructure; neither is "easy"):
  1. **Symmetric powers / Abel maps.** `AJ_d : Symᵈ X → Pic^d`, `D ↦ 𝒪_X(D)`, normalized to
     `Pic⁰` by `D ↦ 𝒪_X(D − d·x₀)`; for `d = g` this is birational and surjective over `k̄`.
     Using it to *construct* `Jac` needs Layer C (Symᵈ existence/smoothness, relative
     effective divisors, semicontinuity, cohomology-and-base-change, descent); it does
     *not* directly "yield" `Jac` by itself.
  2. **General Picard scheme** of a projective variety (Hilbert/Grothendieck), then
     specialize. Even heavier.
- **Properness/projectivity** of `Pic⁰` (not merely representability).

### Layer E, abelian varieties
- **Abelian variety** = smooth, proper, geometrically connected group scheme over `k`;
  basic API, **`dim`**. Commutativity is automatic (rigidity, `Group/Abelian.lean`).
- **Tangent space** `T₀ Pic⁰ ≅ H¹(X, 𝒪_X)`, hence `dim (Jac X) = g`.
- **The theorem of the cube/square**, the **dual abelian variety**, **polarizations** (the
  theta divisor gives `Jac` a principal polarization), and `[n]` as an isogeny. (These are
  *not* needed for the group law on `Pic⁰`, which is tensor product; they belong here, with
  the dual/polarization theory, not at the construction step.)
- **Characteristic `p`:** `p`-torsion is non-étale, isogenies can be inseparable; avoid
  hidden perfect-field assumptions.

### Layer F, Abel–Jacobi and the universal property
- The **Abel–Jacobi morphism** `aj : X ⟶ Jac X`, `x₀ ↦ 0` (the `d = 1` Abel map).
- **Universal property (precise):** for every abelian variety `A` and pointed morphism
  `f : (X, x₀) → (A, 0)`, there is a **unique homomorphism of abelian varieties**
  `φ : Jac X → A` with `f = φ ∘ aj` (the Albanese property; for a curve `Jac = Alb`).
- **Base-change compatibility** along `k → K` (relies on Layer C).

## Acceptance criteria ("checks along the way")

A finished construction must pass sanity checks that rule out vacuous definitions:
- **`dim (Jac X) = genus X`** (via `T₀ Pic⁰ ≅ H¹(X,𝒪_X)`);
- **genus 1:** `Jac (E, O) ≅ E`, reconciled with Mathlib's `E(k)` group law (built via the
  class group / `Pic⁰`);
- **`aj` is a closed immersion for `genus X ≥ 1`** (check after base change to `k̄`, hence
  over `k`);
- base-change compatibility above.

## Scope and caveats (Kevin Buzzard)

- **The `k`-rational point is assumed.** Without it, `x ↦ 𝒪_X(x)` maps `X` into `Pic¹`,
  which is a **torsor under `Pic⁰`** and may have no `k`-point; `Pic⁰` (the Jacobian) still
  *exists*, but `aj` and the clean functor-of-points picture need `x₀`. The torsor / `Pic¹`
  / Albanese-torsor story is the **v2** generalization, out of scope for v1.
- **Jacobian ≠ Albanese in general.** Canonically isomorphic for curves but with *opposite*
  functorialities (`Pic⁰` contravariant; Albanese covariant). Keep them distinct in v2.
- **Imperfect fields:** use "geometrically connected/integral", not bare connectedness;
  watch base-change subtleties throughout Layers C–D.

## References

- R. Hartshorne, *Algebraic Geometry*: Ch. II (sheaves, divisors), III (cohomology,
  incl. III.12 cohomology and base change), IV (curves, Riemann–Roch).
- Q. Liu, *Algebraic Geometry and Arithmetic Curves*: curves, models, Picard.
- J. S. Milne, *Abelian Varieties* and *Jacobian Varieties* (in Cornell–Silverman,
  *Arithmetic Geometry*): the construction and universal property.
- D. Mumford, *Abelian Varieties*: theorem of the cube/square, dual variety, polarizations.
- Bosch–Lütkebohmert–Raynaud, *Néron Models*, Ch. 8–9: the Picard functor and its
  representability.
- The Stacks Project: *Picard schemes of curves* (tag 0B95), *Divisors* (tag 01WP),
  *Cohomology and base change* (tag 0B91), *Quot/Hilbert and Picard functors* (tag 0D04).

## How to drive it

Large by design, expanded **iteratively**. Build Layer A, then B, … ; as each layer makes
the next layer's *types* expressible, state that layer's milestones in `Targets.lean` (with
`sorry`) and hand them to the AIs to discharge in `TauCeti/`. Nothing here blocks on
upstream Mathlib.

## Acknowledgements

This roadmap builds directly on earlier discussions on the [Lean
Zulip](https://leanprover.zulipchat.com/), and would not have been possible without them:

- [#Autoformalization > Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/583336-Autoformalization/topic/Jacobian%20challenge),
  where Kevin Buzzard posed the original Jacobian challenge.
- Private project discussions with Christian Merten, Matthew Ballard, Adam Topaz,
  Fabian Glöckle, and Jack McCarthy; the algebraic-geometry reformulation this roadmap
  follows is due to Christian Merten.

Thanks to everyone who contributed to these discussions.
