/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Functoriality
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import TauCeti.Data.ZMod.PiReduction
import TauCeti.Algebra.Group.PowMonoidHom

/-!
# Points of the formal diagonalizable group

For a commutative group `G` the points of the diagonalizable group `D(G) = Spec R[G]` with values
in a commutative `R`-algebra `A` are the characters `G →* Aˣ`
(`TauCeti.DiagonalizableGroup.pointsMulEquiv`). Given an ideal `I` of `A`, the points that reduce
to the identity modulo `I` are those whose character takes values in the principal unit group
`1 + I` (`Ideal.principalUnitGroup`). They form a subgroup `formalPoints I` of the convolution
group of points, and `formalPointsMulEquiv` identifies it with the characters `G →* 1 + I`.

For a local `𝒪`-algebra `A` and `I = 𝔪_A` this is the functor of points `A ↦ Hom(G, 1 + 𝔪_A)` of
the *formal diagonalizable group* `D̂(G)`, the completion of `D(G)` at the identity of its special
fibre (Khare–Wintenberger, *Serre's modularity conjecture (II)*, §2.5). Specialising to
`G = Multiplicative ℤ` gives `D̂(ℤ)(A) ≃ 1 + 𝔪_A` (`formalPointsIntMulEquiv`), and for finite `ι`
the free abelian group `ℤ ^ ι`, written `Multiplicative (ι → ℤ)`, gives the formal torus.

The second half of the file computes these points on truncated coefficients. If the integer `n`
lies in `I` and `I ^ (m + 1) = 0`, then every element of `1 + I` has order dividing `n ^ m`
(`Ideal.pow_pow_eq_one_of_mem_principalUnitGroup`, from
`(1 + x) ^ (n ^ m) - 1 ∈ (n, x) ^ (m + 1)`). Consequently:

* a homomorphism `π : G →* Q` that is surjective, with kernel contained in the `n ^ m`-th powers,
  induces a bijection of formal points (`formalPointsMulEquivOfKerLe`). For the formal torus
  (`ι` finite) this is the truncation isomorphism `T[n ^ m](A) ≃ T(A)` of Khare–Wintenberger,
  *loc. cit.*, §2.6, proof of Proposition 2.8: on coefficients with `𝔪_A ^ (m + 1) = 0` and
  residue characteristic `p`, the formal points of `(ℤ / p ^ m) ^ ι` and of `ℤ ^ ι` agree
  (`formalPointsTorusTruncationMulEquiv`).
* a group of exponent prime to `n` has no formal points other than the identity
  (`formalPoints_eq_bot_of_coprime`); this is why prime-to-`p` torsion of the character group
  contributes nothing to `D̂(G)`.

The representability of `D̂(G)` by the completion of `𝒪[G]` at the identity of the special fibre is
not part of this file.

## Main definitions

* `TauCeti.DiagonalizableGroup.formalPoints I`: the points of `D(G)` reducing to the identity
  modulo `I`.
* `TauCeti.DiagonalizableGroup.formalPointsMulEquiv I`: these points are the characters
  `G →* 1 + I`.
* `TauCeti.DiagonalizableGroup.formalPointsMap φ`: the pullback of formal points along a group
  homomorphism `φ : G →* Q`.
* `TauCeti.DiagonalizableGroup.formalPointsIntMulEquiv I`: the formal points of `D(ℤ)` are the
  principal units `1 + I`.
* `TauCeti.DiagonalizableGroup.formalPointsMulEquivOfKerLe`: on coefficients with
  `I ^ (m + 1) = 0` and `n ∈ I`, pulling back along a surjection whose kernel consists of
  `n ^ m`-th powers is a bijection of formal points.
* `TauCeti.DiagonalizableGroup.formalPointsTorusTruncationMulEquiv`: the truncation isomorphism
  from the formal points of `D((ℤ / n ^ m) ^ ι)` to those of `D(ℤ ^ ι)`, the formal torus when `ι`
  is finite.

## Main results

* `TauCeti.DiagonalizableGroup.mem_formalPoints`: a point lies in `formalPoints I` exactly when it
  sends every group-like `single g 1` to an element congruent to `1` modulo `I`.
* `TauCeti.DiagonalizableGroup.mapValue_mem_formalPoints`,
  `TauCeti.DiagonalizableGroup.pointsMap_mem_formalPoints`: formal points are functorial in the
  value algebra and contravariantly in the group.
* `TauCeti.DiagonalizableGroup.formalPoints_eq_bot_of_coprime`: groups of exponent prime to `n`
  have only the trivial formal point.

## References

* C. Khare, J.-P. Wintenberger, *Serre's modularity conjecture (II)*, Invent. Math. 178 (2009),
  §2.5 (formal diagonalizable groups) and §2.6, Proposition 2.8 and its proof.
-/

public section

open WithConv

namespace TauCeti

universe u v w w'

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {G : Type w} {Q : Type w'}
variable [CommSemiring R] [CommRing A] [Algebra R A] [CommGroup G] [CommGroup Q]

section FormalPoints

variable (R G) in
/-- The points of the diagonalizable group `D(G)` with values in `A` that reduce to the identity
modulo the ideal `I`: those whose character `G →* Aˣ` takes values in the principal unit group
`1 + I`. For `I` the maximal ideal of an Artinian local `𝒪`-algebra these are the points of the
formal diagonalizable group, the completion of `D(G)` at the identity of its special fibre. -/
def formalPoints (I : Ideal A) : Subgroup (WithConv (MonoidAlgebra R G →ₐ[R] A)) where
  carrier := {f | ∀ g, charOfPoint f.ofConv g ∈ I.principalUnitGroup}
  one_mem' g := by
    rw [← pointsMulEquiv_apply, map_one, MonoidHom.one_apply]
    exact one_mem _
  mul_mem' {f f'} hf hf' g := by
    rw [← pointsMulEquiv_apply, map_mul, MonoidHom.mul_apply]
    exact mul_mem (hf g) (hf' g)
  inv_mem' {f} hf g := by
    rw [← pointsMulEquiv_apply, map_inv, MonoidHom.inv_apply]
    exact inv_mem (hf g)

/-- A point reduces to the identity modulo `I` exactly when its character takes values in the
principal unit group `1 + I`. -/
theorem mem_formalPoints_iff_charOfPoint {I : Ideal A} {f : WithConv (MonoidAlgebra R G →ₐ[R] A)} :
    f ∈ formalPoints R G I ↔ ∀ g, charOfPoint f.ofConv g ∈ I.principalUnitGroup :=
  Iff.rfl

/-- A point reduces to the identity modulo `I` exactly when it sends every group-like
`single g 1` to an element congruent to `1` modulo `I`. -/
theorem mem_formalPoints {I : Ideal A} {f : WithConv (MonoidAlgebra R G →ₐ[R] A)} :
    f ∈ formalPoints R G I ↔ ∀ g, f.ofConv (MonoidAlgebra.single g 1) - 1 ∈ I :=
  forall_congr' fun g ↦ by rw [Ideal.mem_principalUnitGroup, charOfPoint_apply_coe]

/-- Formal points are covariant in the value algebra: an `R`-algebra map `φ : A →ₐ[R] B` carrying
`I` into `J` carries points reducing to the identity modulo `I` to points reducing to the identity
modulo `J`. -/
theorem mapValue_mem_formalPoints {B : Type*} [CommRing B] [Algebra R B] {I : Ideal A}
    {J : Ideal B} (φ : A →ₐ[R] B) (hφ : I ≤ J.comap φ) {f : WithConv (MonoidAlgebra R G →ₐ[R] A)}
    (hf : f ∈ formalPoints R G I) : AlgHom.mapValue φ f ∈ formalPoints R G J := by
  rw [mem_formalPoints]
  intro g
  have h := hφ (mem_formalPoints.mp hf g)
  rw [Ideal.mem_comap, map_sub, map_one] at h
  simpa using h

/-- Formal points are contravariant in the group: precomposing with the map induced by a group
homomorphism `φ : G →* Q` carries formal points of `D(Q)` to formal points of `D(G)`. -/
theorem pointsMap_mem_formalPoints {I : Ideal A} (φ : G →* Q)
    {f : WithConv (MonoidAlgebra R Q →ₐ[R] A)} (hf : f ∈ formalPoints R Q I) :
    pointsMap φ f ∈ formalPoints R G I := by
  refine mem_formalPoints_iff_charOfPoint.mpr fun g ↦ ?_
  rw [← pointsMulEquiv_apply, pointsMulEquiv_pointsMap, MonoidHom.comp_apply]
  exact mem_formalPoints_iff_charOfPoint.mp hf (φ g)

variable (R) in
/-- The pullback of formal points along a group homomorphism `φ : G →* Q`: precomposition with
the map of group algebras induced by `φ`, restricted to the points reducing to the identity
modulo `I`. -/
noncomputable def formalPointsMap (I : Ideal A) (φ : G →* Q) :
    formalPoints R Q I →* formalPoints R G I :=
  ((pointsMap φ).comp (formalPoints R Q I).subtype).codRestrict (formalPoints R G I)
    fun f ↦ pointsMap_mem_formalPoints φ f.property

/-- The pullback of a formal point along `φ` is precomposition with the map of group algebras
induced by `φ`. -/
@[simp]
theorem coe_formalPointsMap_apply (I : Ideal A) (φ : G →* Q) (f : formalPoints R Q I) :
    (formalPointsMap R I φ f : WithConv (MonoidAlgebra R G →ₐ[R] A)) = pointsMap φ f :=
  (rfl)

/-- Pulling back formal points along the identity homomorphism is the identity. -/
@[simp]
theorem formalPointsMap_id (I : Ideal A) :
    formalPointsMap R I (MonoidHom.id G) = MonoidHom.id _ :=
  MonoidHom.ext fun f ↦ Subtype.ext (by simp)

/-- **Contravariant functoriality.** Pulling back formal points along a composite homomorphism is
the composite of the pullbacks, in the opposite order. -/
theorem formalPointsMap_comp {P : Type*} [CommGroup P] (I : Ideal A) (φ : G →* Q) (ψ : Q →* P) :
    formalPointsMap R I (ψ.comp φ) = (formalPointsMap R I φ).comp (formalPointsMap R I ψ) :=
  MonoidHom.ext fun f ↦ Subtype.ext congr($(pointsMap_comp φ ψ) f.val)

variable (R G) in
/-- **The points of the formal diagonalizable group.** The points of `D(G)` reducing to the
identity modulo `I` are the characters of `G` with values in the principal unit group `1 + I`.
For a local `𝒪`-algebra `A` and `I = 𝔪_A` this is `D̂(G)(A) ≃ Hom(G, 1 + 𝔪_A)`. -/
noncomputable def formalPointsMulEquiv (I : Ideal A) :
    formalPoints R G I ≃* (G →* I.principalUnitGroup) where
  toFun f := (pointsMulEquiv f.val).codRestrict I.principalUnitGroup
    (mem_formalPoints_iff_charOfPoint.mp f.property)
  invFun χ := ⟨pointsMulEquiv.symm (I.principalUnitGroup.subtype.comp χ),
    mem_formalPoints_iff_charOfPoint.mpr fun g ↦ by
      rw [← pointsMulEquiv_apply, MulEquiv.apply_symm_apply, MonoidHom.comp_apply]
      exact (χ g).property⟩
  left_inv f := Subtype.ext ((MulEquiv.symm_apply_eq _).mpr (MonoidHom.ext fun _ ↦ rfl))
  right_inv χ := by
    ext g
    simp
  map_mul' f f' := by
    ext g
    simp [MonoidHom.codRestrict_apply]

/-- The character attached to a formal point sends `g` to the value of the point on the
group-like `single g 1`. -/
@[simp]
theorem coe_formalPointsMulEquiv_apply (I : Ideal A) (f : formalPoints R G I) (g : G) :
    ((formalPointsMulEquiv R G I f g : Aˣ) : A) = f.val.ofConv (MonoidAlgebra.single g 1) :=
  (rfl)

/-- The formal point attached to a character `χ : G →* 1 + I` is the point of `D(G)` extending
`χ`. -/
@[simp]
theorem coe_formalPointsMulEquiv_symm_apply (I : Ideal A) (χ : G →* I.principalUnitGroup) :
    ((formalPointsMulEquiv R G I).symm χ : WithConv (MonoidAlgebra R G →ₐ[R] A)) =
      toConv (point (I.principalUnitGroup.subtype.comp χ)) :=
  (rfl)

/-- Under `formalPointsMulEquiv`, the pullback of formal points along `φ : G →* Q` is
precomposition of characters with `φ`. -/
theorem formalPointsMulEquiv_formalPointsMap (I : Ideal A) (φ : G →* Q)
    (f : formalPoints R Q I) :
    formalPointsMulEquiv R G I (formalPointsMap R I φ f) =
      (formalPointsMulEquiv R Q I f).comp φ := by
  ext g
  exact congr((($(pointsMulEquiv_pointsMap φ f.val) g : Aˣ) : A))

variable (R) in
/-- **The formal points of `D(ℤ)`.** The points of `D(Multiplicative ℤ)` reducing to the identity
modulo `I` are the principal units `1 + I`, by evaluation at the group-like element of the
generator. For a local ring this is `D̂(ℤ)(A) = 1 + 𝔪_A`. -/
noncomputable def formalPointsIntMulEquiv (I : Ideal A) :
    formalPoints R (Multiplicative ℤ) I ≃* I.principalUnitGroup :=
  (formalPointsMulEquiv R (Multiplicative ℤ) I).trans (zpowersMulHom _).symm

/-- The principal unit attached to a formal point of `D(ℤ)` is its value on the group-like element
of the generator `1`. -/
@[simp]
theorem coe_formalPointsIntMulEquiv_apply (I : Ideal A) (f : formalPoints R (Multiplicative ℤ) I) :
    ((formalPointsIntMulEquiv R I f : Aˣ) : A) =
      f.val.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) := by
  simp [formalPointsIntMulEquiv]

/-- The formal point of `D(ℤ)` attached to a principal unit `u` sends the group-like element of
`k : ℤ` to `u ^ k`. -/
@[simp]
theorem formalPointsIntMulEquiv_symm_apply_single (I : Ideal A) (u : I.principalUnitGroup)
    (k : ℤ) :
    ((formalPointsIntMulEquiv R I).symm u).val.ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd k) 1) = ((u : Aˣ) ^ k : Aˣ) := by
  simp [formalPointsIntMulEquiv]

end FormalPoints

section Truncation

variable (R) in
/-- **Formal points on truncated coefficients.** Suppose the integer `n` lies in `I` and
`I ^ (m + 1) = 0`, so that `1 + I` has exponent dividing `n ^ m`. Then for a surjective
`π : G →* Q` whose kernel consists of `n ^ m`-th powers, pulling back along `π` is a bijection
from the formal points of `D(Q)` to those of `D(G)`: every character `G →* 1 + I` kills the
`n ^ m`-th powers, so factors uniquely through `π`. -/
noncomputable def formalPointsMulEquivOfKerLe (I : Ideal A) {n m : ℕ} (hn : (n : A) ∈ I)
    (hI : I ^ (m + 1) = ⊥) (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ (powMonoidHom (n ^ m) : G →* G).range) :
    formalPoints R Q I ≃* formalPoints R G I :=
  MulEquiv.ofBijective (formalPointsMap R I π) <| by
    have hbij := MonoidHom.bijective_comp_of_ker_le_range_powMonoidHom π hπ hker
      fun u : I.principalUnitGroup ↦ Subtype.ext (by
        simpa using Ideal.pow_pow_eq_one_of_mem_principalUnitGroup hn hI u.property)
    have heq : ⇑(formalPointsMulEquiv R G I) ∘ formalPointsMap R I π =
        (fun χ : Q →* I.principalUnitGroup ↦ χ.comp π) ∘ ⇑(formalPointsMulEquiv R Q I) :=
      funext (formalPointsMulEquiv_formalPointsMap I π)
    rw [← (formalPointsMulEquiv R G I).bijective.of_comp_iff', heq]
    exact hbij.comp (formalPointsMulEquiv R Q I).bijective

/-- The truncation equivalence is precomposition with the map of group algebras induced by `π`. -/
@[simp]
theorem coe_formalPointsMulEquivOfKerLe_apply (I : Ideal A) {n m : ℕ} (hn : (n : A) ∈ I)
    (hI : I ^ (m + 1) = ⊥) (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ (powMonoidHom (n ^ m) : G →* G).range) (f : formalPoints R Q I) :
    (formalPointsMulEquivOfKerLe R I hn hI π hπ hker f : WithConv (MonoidAlgebra R G →ₐ[R] A)) =
      pointsMap π f :=
  (rfl)

variable (ι : Type*)

variable (R) in
/-- **The truncation isomorphism for the formal torus.** If the integer `n` lies in `I` and
`I ^ (m + 1) = 0`, pulling back along the reduction `ℤ ^ ι → (ℤ / n ^ m) ^ ι` maps the formal points
of `D((ℤ / n ^ m) ^ ι)` bijectively to those of `D(ℤ ^ ι)`. For finite `ι` these are the
`n ^ m`-torsion `T[n ^ m]` of the formal torus `T = D̂(ℤ ^ ι)` and `T` itself. For a local ring
`A` of residue characteristic `p` with `𝔪_A ^ (m + 1) = 0`, this is the isomorphism `T[p ^ m] → T`
on coefficients truncated at level `m + 1` (Khare–Wintenberger, *loc. cit.*, proof of
Proposition 2.8). -/
noncomputable def formalPointsTorusTruncationMulEquiv (I : Ideal A) {n m : ℕ} (hn : (n : A) ∈ I)
    (hI : I ^ (m + 1) = ⊥) :
    formalPoints R (Multiplicative (ι → ZMod (n ^ m))) I ≃*
      formalPoints R (Multiplicative (ι → ℤ)) I :=
  formalPointsMulEquivOfKerLe R I hn hI (ZMod.piReduction ι (n ^ m))
    (ZMod.piReduction_surjective ι _) (ZMod.ker_piReduction ι _).le

/-- The truncation isomorphism for the formal torus is precomposition with the map of group
algebras induced by the reduction `ℤ ^ ι → (ℤ / n ^ m) ^ ι`. -/
@[simp]
theorem coe_formalPointsTorusTruncationMulEquiv_apply (I : Ideal A) {n m : ℕ} (hn : (n : A) ∈ I)
    (hI : I ^ (m + 1) = ⊥) (f : formalPoints R (Multiplicative (ι → ZMod (n ^ m))) I) :
    (formalPointsTorusTruncationMulEquiv R ι I hn hI f :
        WithConv (MonoidAlgebra R (Multiplicative (ι → ℤ)) →ₐ[R] A)) =
      pointsMap (ZMod.piReduction ι (n ^ m)) f :=
  (rfl)

/-- **Prime-to-`n` torsion has no formal points.** If the integer `n` lies in `I`,
`I ^ (m + 1) = 0`, and every element of `G` has order dividing `k` with `k` coprime to `n`, then
the identity is the only point of `D(G)` reducing to the identity modulo `I`. For a local ring of
residue characteristic `p` with nilpotent maximal ideal, this says that the prime-to-`p` torsion
of a character group contributes no points to the formal diagonalizable group. -/
theorem formalPoints_eq_bot_of_coprime (I : Ideal A) {n m k : ℕ} (hn : (n : A) ∈ I)
    (hI : I ^ (m + 1) = ⊥) (hG : ∀ g : G, g ^ k = 1) (hk : k.Coprime n) :
    formalPoints R G I = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have hχ : formalPointsMulEquiv R G I ⟨f, hf⟩ = 1 := by
    ext g
    have hn' : (formalPointsMulEquiv R G I ⟨f, hf⟩ g : Aˣ) ^ n ^ m = 1 :=
      Ideal.pow_pow_eq_one_of_mem_principalUnitGroup hn hI (SetLike.coe_mem _)
    have hk' : (formalPointsMulEquiv R G I ⟨f, hf⟩ g : Aˣ) ^ k = 1 := by
      simpa [hG] using congr((($(map_pow (formalPointsMulEquiv R G I ⟨f, hf⟩) g k)) : Aˣ)).symm
    have h1 := pow_gcd_eq_one.mpr ⟨hk', hn'⟩
    rw [Nat.Coprime.pow_right m hk, pow_one] at h1
    simp [h1]
  simpa using hχ

end Truncation

end DiagonalizableGroup

end TauCeti
