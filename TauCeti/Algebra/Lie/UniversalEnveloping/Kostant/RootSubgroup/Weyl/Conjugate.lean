/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Basic

/-!
# Weyl conjugates of integrally acting elements

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ` and preserve an additive
subgroup `M ≤ V`, and let `(h₀, eᵢ, eⱼ)` be an `sl₂` triple of the Lie algebra `L` whose
raising and lowering elements act nilpotently, both on `L` and on `V`. Its Weyl automorphism
`w = exp (ad eᵢ) ∘ exp (ad (-eⱼ)) ∘ exp (ad eᵢ)` of `L` and Chevalley's Weyl element
`n = x_i(1) x_j(-1) x_i(1)` of the lattice are related, for *every* `x ∈ L`, by

```text
ρ(w x) = n ρ(x) n⁻¹.
```

Since `n` and `n⁻¹` preserve `M`, the divided power `ρ(w x)⁽ᵏ⁾ = n ρ(x)⁽ᵏ⁾ n⁻¹` preserves `M`
whenever `ρ(x)⁽ᵏ⁾` does. If moreover `ρ(x)` is nilpotent, so that the exponential sum is finite,
then over every commutative ring of points the one-parameter subgroups `u ↦ ∑ₖ uᵏ ρ(x)⁽ᵏ⁾` of the
two elements are conjugate:

```text
n x_x(u) n⁻¹ = x_{w x}(u).
```

These are the statements that produce root subgroups at non-simple roots. A root vector `e_γ` of a
Chevalley system is, up to sign, the image of a simple root vector under a product of Weyl
automorphisms of simple roots (Steinberg, Chapter 3). Combined with that description, stability of
divided-power actions under negation (`TauCeti.Associative.dividedPower_neg_smul_mem`) and
under each Weyl automorphism (`TauCeti.UniversalEnvelopingAlgebra.dividedPower_weylAut_smul_mem`)
shows that `e_γ` acts on every Kostant-stable lattice with integral divided powers, and the
conjugation formula expresses the root subgroup of `e_γ` through the simple ones and the Weyl
elements.

Only the generic Weyl-element identity of
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Basic` is used; the triple need
not be the image of an `sl₂` triple in `V`, and `x` need not be a root vector. The identities hold
over every ring of points, in particular in characteristics two and three.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.apply_ι_weylAut_eq_weylUnit_conj`: the action of `w x` is
  the conjugate of the action of `x` by the Weyl element.
* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_weylAut_smul_mem`: a divided power of `w x`
  preserves `M` whenever the same divided power of `x` does.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_conj_baseChangeExp_weylAut`: on points,
  conjugating the one-parameter subgroup of a nilpotently acting `x` by the Weyl element gives
  that of `w x`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open TensorProduct LieAlgebra

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable {i j : ι} {h₀ : L}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (t : IsSl2Triple h₀ (e i) (e j))
variable (hai : IsNilpotent (ad ℚ L (e i))) (haj : IsNilpotent (ad ℚ L (e j)))

/-- **The Weyl element conjugates the action of `x` to that of its Weyl transform.** For the Weyl
automorphism `w` of an `sl₂` triple `(h₀, eᵢ, eⱼ)` of `L` and every `x ∈ L`,
`ρ(w x) = n ρ(x) n⁻¹`, where `n = exp ρ(eᵢ) · exp (-ρ(eⱼ)) · exp ρ(eᵢ)` is the Weyl element of the
Kostant root pair. -/
theorem apply_ι_weylAut_eq_weylUnit_conj (x : L) :
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (weylAut t hai haj x)) =
      ((weylUnit hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) *
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
          (((weylUnit hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) :=
  (ρ.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)).map_weylAut_eq_weylUnit_conj t hai
    haj hi hj x

include hM hi hj

/-- **Weyl transforms of integrally acting elements act integrally.** If the `n`-th divided power
of `ρ(x)` preserves the Kostant-stable subgroup `M`, then so does the `n`-th divided power of
`ρ(w x)`, for the Weyl automorphism `w` of an `sl₂` triple `(h₀, eᵢ, eⱼ)` of `L`: it is the
conjugate of that of `ρ(x)` by the Weyl element, which preserves `M` together with its inverse. -/
theorem dividedPower_weylAut_smul_mem {x : L} (n : ℕ)
    (hx : ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M) :
    ∀ v ∈ M, Associative.dividedPower n
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (weylAut t hai haj x))) • v ∈ M := by
  rw [apply_ι_weylAut_eq_weylUnit_conj e ρ hi hj t hai haj x]
  exact Associative.dividedPower_conj_smul_mem _ (M : Set V) _
    (fun _ hv => weylUnit_smul_mem e h ρ M hM hi hj hv)
    (fun _ hv => inv_weylUnit_smul_mem e h ρ M hM hi hj hv) n hx

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- **Conjugating a one-parameter subgroup by the Weyl element.** Over every ring of points,
`n x_x(u) n⁻¹ = x_{w x}(u)` for an element `x` acting nilpotently on `V` with divided powers
preserving `M`, where `x_y(u) = ∑ₖ uᵏ ρ(y)⁽ᵏ⁾` and `w` is the Weyl automorphism of the `sl₂`
triple `(h₀, eᵢ, eⱼ)` of `L`.

For `x = eᵢ` this recovers `n x_i(u) n⁻¹ = x_j(-u)`
(`TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_conj_baseChangeExp`), since `w eᵢ = -eⱼ`. -/
theorem kostantWeylPoints_conj_baseChangeExp_weylAut {x : L}
    (hx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hxnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x))) (u : A) :
    (kostantWeylPoints e h ρ M hM hi hj A).toLinearMap *
          baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hx u *
        (kostantWeylPoints e h ρ M hM hi hj A).symm.toLinearMap =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (weylAut t hai haj x))) M
        (fun n => dividedPower_weylAut_smul_mem e h ρ M hM hi hj t hai haj n (hx n)) u := by
  have hrestrict : kostantWeylRestrict e h ρ M hM hi hj =
      integralUnitRestrict (weylUnit hi hj) M
        (fun _ hv => weylUnit_smul_mem e h ρ M hM hi hj hv)
        (fun _ hv => inv_weylUnit_smul_mem e h ρ M hM hi hj hv) :=
    LinearEquiv.ext fun v => Subtype.ext (by simp)
  rw [kostantWeylPoints_toLinearMap, kostantWeylPoints_symm_toLinearMap, hrestrict,
    baseChange_integralUnitRestrict_conj_baseChangeExp (R := A) _ M _ _ _ _ hxnil u]
  exact baseChangeExp_congr (apply_ι_weylAut_eq_weylUnit_conj e ρ hi hj t hai haj x).symm M _ _ u

end TauCeti.UniversalEnvelopingAlgebra
