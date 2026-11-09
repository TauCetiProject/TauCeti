/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.Algebra.TensorProduct.Galois

/-!
# Descent of Hopf ideals

A closed subgroup of an affine group over a field `k` is cut out by a Hopf ideal of the coordinate
Hopf algebra `H`. This file identifies the Hopf ideals of a scalar extension `L ⊗[k] H` that come
from Hopf ideals of `H`, that is, the closed subgroups of the base-changed group that are defined
over `k`.

When the ground-field map is surjective, every Hopf ideal after scalar extension comes from a Hopf
ideal over the original field. The coefficient Hopf ideal for the one-element basis supplies the
descent. This applies to an algebraic extension of an algebraically closed field and allows
geometric subgroup conditions to be checked over that field itself.

Along a Galois extension `L / k`, possibly infinite, a Hopf ideal of `L ⊗[k] H` descends exactly
when it is stable under the action of `Gal(L / k)` on the scalar factor. The descended Hopf ideal is
unique, consists of the elements `h` with `1 ⊗ h` in the given ideal, and is the coefficient Hopf
ideal in any basis of `L`. Galois descent of subspaces supplies the underlying ideal, and the
coefficient Hopf ideal supplies the Hopf structure without rechecking it. This is the descent step
for closed subgroups characterized geometrically, such as the unipotent radical, over a perfect
field, whose algebraic closure is Galois.

## Main declarations

* `TauCeti.CommHopfAlgCat.baseChangeHopfIdeal_surjective`: every Hopf ideal descends along a
  surjective map of ground fields.
* `TauCeti.CommHopfAlgCat.map_mem_baseChangeHopfIdeal`: a base-changed Hopf ideal is stable under
  every algebra endomorphism of the scalar factor.
* `Module.Basis.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem`: a Galois-stable Hopf
  ideal is the base change of its coefficient Hopf ideal.
* `Module.Basis.mem_coefficientHopfIdeal_iff_of_forall_map_mem`: that coefficient Hopf ideal
  consists of the elements `h` with `1 ⊗ h` in the Galois-stable Hopf ideal.
* `TauCeti.CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff`: along a Galois extension, the
  base-changed Hopf ideals are exactly the Galois-stable ones, each descending uniquely.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §AG.14.
* J. S. Milne, *Algebraic Groups* (2017), Appendix A.
-/

public section

open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

section Surjective

variable {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- Every Hopf ideal descends along a surjective map of ground fields. -/
theorem baseChangeHopfIdeal_surjective (h : Function.Surjective (algebraMap k K)) :
    Function.Surjective (baseChangeHopfIdeal (H := H) (K := K)) := by
  classical
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    ⟨(algebraMap k K).injective, h⟩
  let b := (Module.Basis.singleton Unit k).map e.toLinearEquiv
  have hb (j : Unit) : b j = 1 := by
    simp only [b, Module.Basis.map_apply, Module.Basis.singleton_apply,
      AlgEquiv.toLinearEquiv_apply, map_one]
  have coefficient_one_tmul (x : H) (j : Unit) :
      TensorProduct.equivFinsuppOfBasisLeft b (1 ⊗ₜ[k] x) j = x := by
    rw [← hb j, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp
  intro I
  refine ⟨b.coefficientHopfIdeal I, le_antisymm ?_ ?_⟩
  · rw [← HopfIdeal.toIdeal_le_toIdeal, baseChangeHopfIdeal_toIdeal,
      Ideal.map_le_iff_le_comap, Module.Basis.coefficientHopfIdeal_toIdeal_le_iff]
    intro z hz j
    obtain ⟨x, rfl⟩ := Algebra.TensorProduct.includeRight_surjective (T := H) h z
    simpa only [Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply,
      coefficient_one_tmul, HopfIdeal.mem_toIdeal] using hz
  · exact (b.coefficientHopfIdeal_le_iff_le_baseChangeHopfIdeal I _).mp le_rfl

end Surjective

section Stable

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- The base change of a Hopf ideal is stable under every algebra endomorphism of the scalar
factor, in particular under the Galois action when `K / k` is a field extension. -/
theorem map_mem_baseChangeHopfIdeal (J : HopfIdeal k H) (φ : K →ₐ[k] K) {x : K ⊗[k] H}
    (hx : x ∈ baseChangeHopfIdeal (K := K) J) :
    TensorProduct.map φ.toLinearMap LinearMap.id x ∈ baseChangeHopfIdeal (K := K) J := by
  let g : K ⊗[k] H →ₐ[k] K ⊗[k] H := Algebra.TensorProduct.map φ (AlgHom.id k H)
  rw [← HopfIdeal.mem_toIdeal, baseChangeHopfIdeal_toIdeal] at hx ⊢
  have hle : J.toIdeal.map (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) ≤
      (J.toIdeal.map (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H)).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    simpa [g] using Ideal.mem_map_of_mem Algebra.TensorProduct.includeRight hh
  exact hle hx

end Stable

section Galois

variable {k : Type u} {L : Type w} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- For a Galois-stable Hopf ideal `I` of `L ⊗[k] H`, every coefficient `c` of an element of `I`,
in a basis of `L`, satisfies `1 ⊗ c ∈ I`. -/
private theorem one_tmul_equivFinsuppOfBasisLeft_mem {κ : Type*} [DecidableEq κ]
    (b : Module.Basis κ k L) (I : HopfIdeal L (baseChange (K := L) H))
    (hI : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I)
    {z : L ⊗[k] H} (hz : z ∈ I) (j : κ) :
    1 ⊗ₜ[k] TensorProduct.equivFinsuppOfBasisLeft b z j ∈ I := by
  let W : Submodule L (L ⊗[k] H) := I.toIdeal.restrictScalars L
  let p := (W.restrictScalars k).comap (TensorProduct.mk k L H 1)
  have hz : z ∈ p.baseChange L := by
    rw [W.baseChange_comap_eq_of_forall_map_mem hI]
    exact HopfIdeal.mem_toIdeal.mpr hz
  obtain ⟨y, rfl⟩ := hz
  -- The coefficients of an element of `p.baseChange L` lie in `p`.
  have hy := b.equivFinsuppOfBasisLeft_lTensor_apply p.subtype y j
  exact HopfIdeal.mem_toIdeal.mp (hy ▸ (TensorProduct.equivFinsuppOfBasisLeft b y j).2)

/-- **Galois descent of Hopf ideals.** Along a Galois extension `L / k`, a Hopf ideal of
`L ⊗[k] H` stable under the scalar-factor Galois action is the base change of its coefficient Hopf
ideal in any basis of `L`. -/
theorem _root_.Module.Basis.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem
    {κ : Type*} [DecidableEq κ] (b : Module.Basis κ k L)
    (I : HopfIdeal L (baseChange (K := L) H))
    (hI : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I) :
    baseChangeHopfIdeal (K := L) (b.coefficientHopfIdeal I) = I := by
  refine le_antisymm ?_ ((b.coefficientHopfIdeal_le_iff_le_baseChangeHopfIdeal I _).mp le_rfl)
  rw [← HopfIdeal.toIdeal_le_toIdeal, baseChangeHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap,
    b.coefficientHopfIdeal_toIdeal_le_iff]
  intro z hz j
  exact HopfIdeal.mem_toIdeal.mpr (one_tmul_equivFinsuppOfBasisLeft_mem b I hI hz j)

/-- The Hopf ideal descended from a Galois-stable Hopf ideal `I` of `L ⊗[k] H` consists of the
elements `h` of `H` with `1 ⊗ h ∈ I`. -/
theorem _root_.Module.Basis.mem_coefficientHopfIdeal_iff_of_forall_map_mem
    {κ : Type*} [DecidableEq κ] (b : Module.Basis κ k L)
    (I : HopfIdeal L (baseChange (K := L) H))
    (hI : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I)
    (h : H) : h ∈ b.coefficientHopfIdeal I ↔ 1 ⊗ₜ[k] h ∈ I := by
  conv_rhs => rw [← b.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem I hI,
    b.mem_baseChangeHopfIdeal_iff]
  refine ⟨fun hh j ↦ ?_, fun hh ↦ ?_⟩
  · rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    exact ((b.coefficientHopfIdeal I).toIdeal.restrictScalars k).smul_mem _ hh
  · -- Some coordinate `c` of `1` in the basis is nonzero, and `c • h` is a coefficient of `1 ⊗ h`.
    obtain ⟨j, hj⟩ : ∃ j, b.repr 1 j ≠ 0 := by
      by_contra! h0
      exact one_ne_zero (b.repr.injective (Finsupp.ext fun j ↦ by simp [h0 j]))
    have hcoeff := hh j
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at hcoeff
    simpa [smul_smul, inv_mul_cancel₀ hj] using
      ((b.coefficientHopfIdeal I).toIdeal.restrictScalars k).smul_mem (b.repr 1 j)⁻¹ hcoeff

/-- Along a Galois extension `L / k`, a Hopf ideal of `L ⊗[k] H` is the base change of a Hopf ideal
of `H` exactly when it is stable under the scalar-factor Galois action, and that Hopf ideal of `H`
is then unique. Geometrically, a closed subgroup of the base-changed group is defined over `k`
exactly when it is stable under `Gal(L / k)`. -/
theorem existsUnique_baseChangeHopfIdeal_eq_iff (I : HopfIdeal L (baseChange (K := L) H)) :
    (∃! J : HopfIdeal k H, baseChangeHopfIdeal (K := L) J = I) ↔
      ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I := by
  constructor
  · rintro ⟨J, rfl, -⟩ σ x hx
    exact map_mem_baseChangeHopfIdeal J σ.toAlgHom hx
  · intro hI
    classical
    let b := Module.Free.chooseBasis k L
    have hb := b.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem I hI
    exact ⟨b.coefficientHopfIdeal I, hb, fun J hJ ↦
      baseChangeHopfIdeal_injective (hJ.trans hb.symm)⟩

end Galois

end TauCeti.CommHopfAlgCat
