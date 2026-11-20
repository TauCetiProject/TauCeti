/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Functoriality
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import Mathlib.Data.ZMod.Basic

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
`G = Multiplicative ℤ` gives `D̂(ℤ)(A) ≃ 1 + 𝔪_A` (`formalPointsIntMulEquiv`), and the free group
`Multiplicative (ι → ℤ)` gives the formal torus.

The second half of the file computes these points on truncated coefficients. If the integer `n`
lies in `I` and `I ^ (m + 1) = 0`, then every element of `1 + I` has order dividing `n ^ m`
(`Ideal.pow_pow_eq_one_of_mem_principalUnitGroup`, from
`(1 + x) ^ (n ^ m) - 1 ∈ (n, x) ^ (m + 1)`). Consequently:

* a homomorphism `π : G →* Q` that is surjective, with kernel contained in the `n ^ m`-th powers,
  induces a bijection of formal points (`formalPointsMulEquivOfKerLe`). For the formal torus this
  is the truncation isomorphism `T[n ^ m](A) ≃ T(A)` of Khare–Wintenberger, *loc. cit.*, §2.6,
  proof of Proposition 2.8: on coefficients with `𝔪_A ^ (m + 1) = 0` and residue characteristic
  `p`, the formal points of `(ℤ / p ^ m) ^ ι` and of `ℤ ^ ι` agree
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
* `TauCeti.DiagonalizableGroup.formalPointsIntMulEquiv I`: the formal points of `D(ℤ)` are the
  principal units `1 + I`.
* `TauCeti.DiagonalizableGroup.formalPointsMulEquivOfKerLe`: on coefficients with
  `I ^ (m + 1) = 0` and `n ∈ I`, pulling back along a surjection whose kernel consists of
  `n ^ m`-th powers is a bijection of formal points.
* `TauCeti.DiagonalizableGroup.formalPointsTorusTruncationMulEquiv`: the truncation isomorphism
  from the formal points of `(ℤ / n ^ m) ^ ι` to those of the formal torus `ℤ ^ ι`.

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
  intro g
  have h := hφ (mem_formalPoints.mp hf g)
  rw [Ideal.mem_comap, map_sub, map_one] at h
  simpa [mem_formalPoints] using h

/-- Formal points are contravariant in the group: precomposing with the map induced by a group
homomorphism `φ : G →* Q` carries formal points of `D(Q)` to formal points of `D(G)`. -/
theorem pointsMap_mem_formalPoints {I : Ideal A} (φ : G →* Q)
    {f : WithConv (MonoidAlgebra R Q →ₐ[R] A)} (hf : f ∈ formalPoints R Q I) :
    pointsMap φ f ∈ formalPoints R G I := by
  intro g
  rw [← pointsMulEquiv_apply, pointsMulEquiv_pointsMap, MonoidHom.comp_apply]
  exact hf (φ g)

variable (R G) in
/-- **The points of the formal diagonalizable group.** The points of `D(G)` reducing to the
identity modulo `I` are the characters of `G` with values in the principal unit group `1 + I`.
For a local `𝒪`-algebra `A` and `I = 𝔪_A` this is `D̂(G)(A) ≃ Hom(G, 1 + 𝔪_A)`. -/
noncomputable def formalPointsMulEquiv (I : Ideal A) :
    formalPoints R G I ≃* (G →* I.principalUnitGroup) where
  toFun f := (pointsMulEquiv f.1).codRestrict I.principalUnitGroup f.2
  invFun χ := ⟨pointsMulEquiv.symm (I.principalUnitGroup.subtype.comp χ), fun g ↦ by
    rw [← pointsMulEquiv_apply, MulEquiv.apply_symm_apply, MonoidHom.comp_apply]
    exact (χ g).2⟩
  left_inv f := Subtype.ext ((MulEquiv.symm_apply_eq _).mpr rfl)
  right_inv χ := by
    ext g
    simp
  map_mul' f f' := by
    ext g
    simp [MonoidHom.codRestrict]

/-- The character attached to a formal point sends `g` to the value of the point on the
group-like `single g 1`. -/
@[simp]
theorem coe_formalPointsMulEquiv_apply (I : Ideal A) (f : formalPoints R G I) (g : G) :
    ((formalPointsMulEquiv R G I f g : Aˣ) : A) = f.1.ofConv (MonoidAlgebra.single g 1) :=
  (rfl)

/-- The formal point attached to a character `χ : G →* 1 + I` is the point of `D(G)` extending
`χ`. -/
@[simp]
theorem coe_formalPointsMulEquiv_symm_apply (I : Ideal A) (χ : G →* I.principalUnitGroup) :
    ((formalPointsMulEquiv R G I).symm χ : WithConv (MonoidAlgebra R G →ₐ[R] A)) =
      toConv (point (I.principalUnitGroup.subtype.comp χ)) :=
  (rfl)

/-- Under `formalPointsMulEquiv`, precomposition of points with the map induced by `φ : G →* Q`
is precomposition of characters with `φ`. -/
theorem formalPointsMulEquiv_pointsMap (I : Ideal A) (φ : G →* Q) (f : formalPoints R Q I) :
    formalPointsMulEquiv R G I ⟨pointsMap φ f, pointsMap_mem_formalPoints φ f.2⟩ =
      (formalPointsMulEquiv R Q I f).comp φ := by
  ext g
  rw [coe_formalPointsMulEquiv_apply, MonoidHom.comp_apply, coe_formalPointsMulEquiv_apply,
    ← charOfPoint_apply_coe, ← pointsMulEquiv_apply, pointsMulEquiv_pointsMap,
    MonoidHom.comp_apply, pointsMulEquiv_apply, charOfPoint_apply_coe]

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
      f.1.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) := by
  simp [formalPointsIntMulEquiv, zpowersMulHom, zpowersHom]

end FormalPoints

section Truncation

/-- Precomposition with a surjective homomorphism `π : G →* Q` whose kernel consists of `k`-th
powers is a bijection onto the homomorphisms `G →* U`, when `U` has exponent dividing `k`. -/
private theorem bijective_comp_of_ker_le {U : Type*} [Group U] {k : ℕ} (π : G →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ (powMonoidHom k : G →* G).range)
    (hU : ∀ u : U, u ^ k = 1) : Function.Bijective fun χ : Q →* U ↦ χ.comp π := by
  refine ⟨fun χ χ' h ↦ (MonoidHom.cancel_right hπ).mp h, fun χ ↦ ?_⟩
  have hle : π.ker ≤ χ.ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := hker hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hU]
  exact ⟨π.liftOfSurjective hπ ⟨χ, hle⟩, π.liftOfRightInverse_comp _ _ ⟨χ, hle⟩⟩

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
  MulEquiv.ofBijective
    (((pointsMap π).comp (formalPoints R Q I).subtype).codRestrict (formalPoints R G I)
      fun f ↦ pointsMap_mem_formalPoints π f.2) <| by
    have hbij := bijective_comp_of_ker_le π hπ hker fun u : I.principalUnitGroup ↦
      Subtype.ext (by
        simpa using Ideal.pow_pow_eq_one_of_mem_principalUnitGroup hn hI u.2)
    have heq : ⇑(formalPointsMulEquiv R G I) ∘
        (((pointsMap π).comp (formalPoints R Q I).subtype).codRestrict (formalPoints R G I)
          fun f ↦ pointsMap_mem_formalPoints π f.2) =
        (fun χ : Q →* I.principalUnitGroup ↦ χ.comp π) ∘ ⇑(formalPointsMulEquiv R Q I) := by
      funext f
      exact formalPointsMulEquiv_pointsMap I π f
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

variable (ι : Type*) (k : ℕ)

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι`, written multiplicatively: the map of character groups
dual to the inclusion of the `k`-torsion `T[k]` of the formal torus `T = D̂(ℤ ^ ι)`. -/
noncomputable def torusReduction :
    Multiplicative (ι → ℤ) →* Multiplicative (ι → ZMod k) :=
  AddMonoidHom.toMultiplicative ((Int.castAddHom (ZMod k)).compLeft ι)

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι` reduces each coordinate modulo `k`. -/
@[simp]
theorem torusReduction_apply (x : Multiplicative (ι → ℤ)) (i : ι) :
    (torusReduction ι k x).toAdd i = (x.toAdd i : ZMod k) :=
  (rfl)

/-- The reduction `ℤ ^ ι → (ℤ / k) ^ ι` is surjective. -/
theorem torusReduction_surjective : Function.Surjective (torusReduction ι k) := by
  intro y
  refine ⟨Multiplicative.ofAdd fun i ↦ (y.toAdd i).cast, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp

/-- The kernel of the reduction `ℤ ^ ι → (ℤ / k) ^ ι` consists of the `k`-th powers. -/
theorem ker_torusReduction_le :
    (torusReduction ι k).ker ≤ (powMonoidHom k : Multiplicative (ι → ℤ) →* _).range := by
  intro x hx
  have hdvd (i : ι) : (k : ℤ) ∣ x.toAdd i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← torusReduction_apply]
    exact congrFun (congrArg Multiplicative.toAdd hx) i
  choose y hy using hdvd
  refine ⟨Multiplicative.ofAdd y, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp [hy i]

variable (R) in
/-- **The truncation isomorphism for the formal torus.** If the integer `n` lies in `I` and
`I ^ (m + 1) = 0`, the formal points of the `n ^ m`-torsion `T[n ^ m] = D̂((ℤ / n ^ m) ^ ι)` of the
formal torus `T = D̂(ℤ ^ ι)` map bijectively to those of `T`. For a local ring `A` of residue
characteristic `p` with `𝔪_A ^ (m + 1) = 0`, this is the isomorphism `T[p ^ m] → T` on coefficients
truncated at level `m + 1` (Khare–Wintenberger, *loc. cit.*, proof of Proposition 2.8). -/
noncomputable def formalPointsTorusTruncationMulEquiv (I : Ideal A) {n m : ℕ} (hn : (n : A) ∈ I)
    (hI : I ^ (m + 1) = ⊥) :
    formalPoints R (Multiplicative (ι → ZMod (n ^ m))) I ≃*
      formalPoints R (Multiplicative (ι → ℤ)) I :=
  formalPointsMulEquivOfKerLe R I hn hI (torusReduction ι (n ^ m))
    (torusReduction_surjective ι _) (ker_torusReduction_le ι _)

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
      rw [← Subgroup.coe_pow, ← map_pow, hG, map_one, OneMemClass.coe_one]
    have h1 := pow_gcd_eq_one.mpr ⟨hk', hn'⟩
    rw [Nat.Coprime.pow_right m hk, pow_one] at h1
    simp [h1]
  exact congrArg Subtype.val ((formalPointsMulEquiv R G I).injective
    (hχ.trans (map_one (formalPointsMulEquiv R G I)).symm))

end Truncation

end DiagonalizableGroup

end TauCeti
