/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Invertible
public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Determinant lines of modules and of linear maps

The *determinant line* of a module `V` of rank `n` is its top exterior power `⋀ⁿ V`
(`TauCeti.detLine`). For a finite free module it is free of rank one. A linear isomorphism
`e : V ≃ W` induces an isomorphism of determinant lines sending `v₁ ∧ ⋯ ∧ vₙ` to
`e v₁ ∧ ⋯ ∧ e vₙ` (`LinearEquiv.detLineCongr`), functorially. A module of rank zero has determinant
line canonically `R`, the empty wedge product going to `1`
(`TauCeti.detLineEquivOfFinrankEqZero`).

The determinant line of a linear map `f : M → N` is
`det (ker f) ⊗ (det (coker f))^*` (`LinearMap.detLine`), with the cokernel `N ⧸ range f`. When
kernel and cokernel are finite-dimensional, for example for a Fredholm operator, it is a line
(`LinearMap.finrank_detLine`). Orientations of moduli spaces in Morse and Floer theory are
orientations of these lines for the linearized operators: as the operator varies, kernel and
cokernel jump, but the determinant lines fit together into a line bundle, a construction not
carried out here. This file sets up the pointwise object:

* an isomorphism `f.detLine ≃ R` when `f` is bijective (`LinearMap.detLineEquivOfBijective`);
* the transport of determinant lines along a commuting square whose horizontal sides are linear
  isomorphisms (`LinearMap.detLineCongr`), which is how a change of trivialization acts.

An automorphism of a free module acts on its determinant line by its determinant
(`LinearEquiv.detLineCongr_apply_eq_det_smul`). Consequently, automorphisms `e₁` of the source and
`e₂` of the target of `f` commuting with `f` act on the determinant line of `f` by
`det k₁ * (det k₂)⁻¹`, where `k₁` and `k₂` are the automorphisms they induce on the kernel and on
the cokernel (`LinearMap.detLineCongr_apply_eq_det_smul`). If a unit `c` acts by multiplication
on both the source and the target of `f`, the induced transport of the determinant line of `f` is
multiplication by `c ^ ind f`, with `ind f = dim (ker f) - dim (coker f)`
(`LinearMap.detLineCongr_apply_of_forall_eq_smul`). For `c = -1` this is the sign
`(-1) ^ (dim (ker f) + dim (coker f))` (`LinearMap.detLineCongr_neg_apply`); for instance, complex
conjugation of a connection acts on its imaginary-valued deformations, and on the determinant line
of the real deformation operator, by this sign. This application to charge conjugation in
Seiberg–Witten theory follows [Taubes, *SW ⇒ Gr*] and [Morgan, *The Seiberg–Witten equations*];
the linear algebra itself is standard.

## Main definitions

* `TauCeti.detLine R V`: the top exterior power `⋀[R]^(finrank R V) V`.
* `LinearEquiv.detLineCongr`: the isomorphism of determinant lines induced by `V ≃ₗ[R] W`.
* `TauCeti.detLineEquivOfFinrankEqZero`: the determinant line of a rank-zero module is `R`.
* `LinearMap.detLine f`: the determinant line `det (ker f) ⊗ (det (N ⧸ range f))^*` of `f`.
* `LinearMap.detLineEquivOfBijective`: the determinant line of a bijective map is `R`.
* `LinearMap.detLineCongr`: transport of determinant lines along a commuting square.

## Main results

* `TauCeti.finrank_detLine`: the determinant line of a finite free module has rank one.
* `TauCeti.instInvertibleDetLine`: the determinant line of a finite free module is an invertible
  module.
* `LinearEquiv.detLineCongr_refl`, `LinearEquiv.detLineCongr_trans`,
  `LinearEquiv.detLineCongr_symm`: the induced isomorphisms are functorial.
* `LinearEquiv.detLineCongr_apply_eq_det_smul`: an automorphism acts on the determinant line by
  its determinant.
* `LinearMap.finrank_detLine`: the determinant line of a linear map between vector spaces with
  finite-dimensional kernel and cokernel has dimension one.
* `LinearMap.detLineCongr_refl`, `LinearMap.detLineCongr_trans` and `LinearMap.detLineCongr_symm`:
  transport along commuting squares is functorial.
* `LinearMap.detLineCongr_apply_eq_det_smul`: automorphisms of source and target act on the
  determinant line by the determinant on the kernel times the inverse determinant on the cokernel.
* `LinearMap.detLineCongr_apply_of_forall_eq_smul`: multiplication by a unit `c` on source and
  target acts on the determinant line by `c ^ ind f`.
* `LinearMap.detLineCongr_neg_apply`: negation of source and target acts on the determinant line
  by `(-1) ^ (dim (ker f) + dim (coker f))`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996) (charge conjugation).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (charge conjugation).
* D. Quillen, *Determinants of Cauchy–Riemann operators over a Riemann surface*,
  Funct. Anal. Appl. **19** (1985), 31–34.
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V]

/-- The **determinant line** of a module `V` of rank `n`: its top exterior power `⋀ⁿ V`. For a
finite free module it is free of rank one (`TauCeti.finrank_detLine`). -/
abbrev detLine : Type _ := ⋀[R]^(finrank R V) V

/-- The determinant line of a finite free module has rank one. -/
theorem finrank_detLine [Nontrivial R] [Module.Free R V] [Module.Finite R V] :
    finrank R (detLine R V) = 1 := by
  simp [detLine]

/-- The determinant line of a finite free module is an invertible module, so that it cancels
against its dual: `det V ⊗ (det V)^* ≃ R` (`Module.Invertible.linearEquiv`). -/
instance instInvertibleDetLine [Module.Free R V] [Module.Finite R V] :
    Module.Invertible R (detLine R V) :=
  exteriorPower.invertible_of_rankAtStalk_eq fun p ↦ by simp

end TauCeti

namespace LinearEquiv

open TauCeti

variable {R : Type*} [CommRing R] {V W U : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]

/-- The isomorphism of determinant lines `det V ≃ det W` induced by a linear isomorphism
`e : V ≃ W`. It sends `v₁ ∧ ⋯ ∧ vₙ` to `e v₁ ∧ ⋯ ∧ e vₙ` (`LinearEquiv.detLineCongr_ιMulti`). -/
def detLineCongr (e : V ≃ₗ[R] W) : detLine R V ≃ₗ[R] detLine R W :=
  (e.exteriorPower _).trans (LinearEquiv.ofEq _ _ (congrArg (⋀[R]^· W) e.finrank_eq))

@[simp]
theorem detLineCongr_ιMulti (e : V ≃ₗ[R] W) (v : Fin (finrank R V) → V) :
    detLineCongr e (exteriorPower.ιMulti R _ v) =
      exteriorPower.ιMulti R _ (e ∘ v ∘ Fin.cast e.finrank_eq.symm) := by
  rw [detLineCongr, LinearEquiv.trans_apply, exteriorPower_apply_ιMulti,
    exteriorPower.ofEq_ιMulti e.finrank_eq, Function.comp_assoc]

/-- Under the inclusion of the determinant line into the exterior algebra,
`LinearEquiv.detLineCongr` is the algebra map induced by `e`. -/
@[simp]
theorem coe_detLineCongr (e : V ≃ₗ[R] W) (x : detLine R V) :
    (detLineCongr e x : ExteriorAlgebra R W) = ExteriorAlgebra.map e.toLinearMap x := by
  rw [detLineCongr, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact exteriorPower.coe_map _ x

@[simp]
theorem detLineCongr_refl : detLineCongr (LinearEquiv.refl R V) = LinearEquiv.refl R _ := by
  ext x
  simp

@[simp]
theorem detLineCongr_trans (e : V ≃ₗ[R] W) (e' : W ≃ₗ[R] U) :
    detLineCongr (e.trans e') = (detLineCongr e).trans (detLineCongr e') := by
  ext x
  simp [← LinearEquiv.comp_coe, ← ExteriorAlgebra.map_comp_map]

@[simp]
theorem detLineCongr_symm (e : V ≃ₗ[R] W) : (detLineCongr e).symm = detLineCongr e.symm := by
  refine LinearEquiv.ext fun x ↦ ?_
  rw [LinearEquiv.symm_apply_eq, ← LinearEquiv.trans_apply, ← detLineCongr_trans]
  simp

/-- An automorphism of a free module acts on its determinant line by multiplication by its
determinant. -/
theorem detLineCongr_apply_eq_det_smul [Module.Free R V] (e : V ≃ₗ[R] V) (x : detLine R V) :
    detLineCongr e x = LinearMap.det (e : V →ₗ[R] V) • x := by
  refine Subtype.ext ?_
  rw [coe_detLineCongr, ← exteriorPower.coe_map, LinearMap.map_exteriorPower_finrank_eq_det_smul]
  simp

end LinearEquiv

namespace TauCeti

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- The determinant line of a module of rank zero is `R`: the empty exterior product goes to `1`
(`TauCeti.detLineEquivOfFinrankEqZero_ιMulti`). -/
def detLineEquivOfFinrankEqZero (h : finrank R V = 0) : detLine R V ≃ₗ[R] R :=
  (LinearEquiv.ofEq _ _ (congrArg (⋀[R]^· V) h)).trans (exteriorPower.zeroEquiv R V)

@[simp]
theorem detLineEquivOfFinrankEqZero_ιMulti (h : finrank R V = 0) (v : Fin (finrank R V) → V) :
    detLineEquivOfFinrankEqZero h (exteriorPower.ιMulti R _ v) = 1 := by
  rw [detLineEquivOfFinrankEqZero, LinearEquiv.trans_apply, exteriorPower.ofEq_ιMulti h,
    exteriorPower.zeroEquiv_ιMulti]

/-- The inverse sends `1` to the empty exterior product, the canonical generator of the
determinant line of a rank-zero module. -/
@[simp]
theorem detLineEquivOfFinrankEqZero_symm_one (h : finrank R V = 0) :
    (detLineEquivOfFinrankEqZero h).symm 1 = exteriorPower.ιMulti R _ (Fin.elim0 ∘ Fin.cast h) := by
  rw [LinearEquiv.symm_apply_eq, detLineEquivOfFinrankEqZero_ιMulti]

end TauCeti

namespace LinearMap

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

variable (f : M →ₗ[R] N) in
/-- The **determinant line** `det (ker f) ⊗ (det (coker f))^*` of a linear map `f : M → N`, where
the cokernel is `N ⧸ range f`. When kernel and cokernel are finite-dimensional vector spaces it is
a line (`LinearMap.finrank_detLine`). -/
abbrev detLine : Type _ :=
  TauCeti.detLine R (ker f) ⊗[R] Dual R (TauCeti.detLine R (N ⧸ range f))

section CommRing

variable {M' N' M'' N'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  [AddCommGroup M''] [Module R M''] [AddCommGroup N''] [Module R N''] {f : M →ₗ[R] N}

/-- The determinant line of a bijective linear map is `R`. Kernel and cokernel are zero, so their
determinant lines are spanned by empty exterior products; the isomorphism sends `1 ⊗ φ` to the
value of `φ` on the empty exterior product of the cokernel
(`LinearMap.detLineEquivOfBijective_tmul_ιMulti`). -/
def detLineEquivOfBijective [Nontrivial R] (hf : Function.Bijective f) : f.detLine ≃ₗ[R] R :=
  have hker : finrank R (ker f) = 0 := by
    have : Subsingleton (ker f) := Submodule.subsingleton_iff_eq_bot.mpr (ker_eq_bot.mpr hf.1)
    exact finrank_zero_of_subsingleton
  have hcoker : finrank R (N ⧸ range f) = 0 := by
    have : Subsingleton (N ⧸ range f) :=
      Submodule.Quotient.subsingleton_iff.mpr (range_eq_top.mpr hf.2)
    exact finrank_zero_of_subsingleton
  (TensorProduct.congr (TauCeti.detLineEquivOfFinrankEqZero hker)
      ((TauCeti.detLineEquivOfFinrankEqZero hcoker).symm.dualMap.trans
        (ringLmapEquivSelf R R R))).trans
    (TensorProduct.lid R R)

/-- The cokernel of a bijective map is zero, so every family `w` indexed by `Fin 0` gives the empty
exterior product, at which the functional `φ` is evaluated. -/
theorem detLineEquivOfBijective_tmul_ιMulti [Nontrivial R] (hf : Function.Bijective f)
    (v : Fin (finrank R (ker f)) → ker f)
    (φ : Dual R (TauCeti.detLine R (N ⧸ range f)))
    (w : Fin (finrank R (N ⧸ range f)) → N ⧸ range f) :
    detLineEquivOfBijective hf (exteriorPower.ιMulti R _ v ⊗ₜ φ) =
      φ (exteriorPower.ιMulti R _ w) := by
  simp only [detLineEquivOfBijective, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TauCeti.detLineEquivOfFinrankEqZero_ιMulti, TensorProduct.lid_tmul, one_smul,
    ringLmapEquivSelf_apply, LinearEquiv.dualMap_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq, TauCeti.detLineEquivOfFinrankEqZero_ιMulti]

/-- The inverse sends `1` to `v ⊗ φ`, for the empty exterior product `v` of the kernel and any
functional `φ` taking the value `1` on the empty exterior product of the cokernel. -/
theorem detLineEquivOfBijective_symm_one [Nontrivial R] (hf : Function.Bijective f)
    (v : Fin (finrank R (ker f)) → ker f) (φ : Dual R (TauCeti.detLine R (N ⧸ range f)))
    (w : Fin (finrank R (N ⧸ range f)) → N ⧸ range f) (hφ : φ (exteriorPower.ιMulti R _ w) = 1) :
    (detLineEquivOfBijective hf).symm 1 = exteriorPower.ιMulti R _ v ⊗ₜ φ := by
  rw [LinearEquiv.symm_apply_eq, detLineEquivOfBijective_tmul_ιMulti hf v φ w, hφ]

/-- The transport of determinant lines along a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps
with `e₁` and `e₂` linear isomorphisms. It is the tensor product of the isomorphism of kernel
determinant lines induced by `e₁` and the dual of the inverse of the isomorphism of cokernel
determinant lines induced by `e₂` (`LinearMap.detLineCongr_tmul`). -/
def detLineCongr (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) : f.detLine ≃ₗ[R] g.detLine :=
  TensorProduct.congr
    (LinearEquiv.detLineCongr
      (e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)))
    (LinearEquiv.detLineCongr
      (Submodule.Quotient.equiv _ _ e₂
        (f.map_range_eq_range_of_comp_eq e₁.surjective h))).symm.dualMap

@[simp]
theorem detLineCongr_tmul (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M')
    (e₂ : N ≃ₗ[R] N') (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
    (x : TauCeti.detLine R (ker f)) (φ : Dual R (TauCeti.detLine R (N ⧸ range f))) :
    f.detLineCongr e₁ e₂ h (x ⊗ₜ φ) =
      LinearEquiv.detLineCongr
          (e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)) x ⊗ₜ
        (φ ∘ₗ (LinearEquiv.detLineCongr (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective h))).symm.toLinearMap) :=
  (rfl)

/-- Transport along the identity square is the identity. -/
@[simp]
theorem detLineCongr_refl :
    f.detLineCongr (LinearEquiv.refl R M) (LinearEquiv.refl R N)
      (by rw [LinearEquiv.refl_toLinearMap, LinearEquiv.refl_toLinearMap, comp_id, id_comp]) =
      LinearEquiv.refl R _ := by
  have hk : (LinearEquiv.refl R M).ofSubmodules (ker f) (ker f)
      (f.map_ker_eq_ker_of_comp_eq (LinearEquiv.refl R M).surjective
        (LinearEquiv.refl R N).injective (by simp)) =
        LinearEquiv.refl R _ := by
    ext x
    simp only [LinearEquiv.ofSubmodules_apply, LinearEquiv.refl_apply]
  have hc : Submodule.Quotient.equiv (range f) (range f) (LinearEquiv.refl R N)
      (f.map_range_eq_range_of_comp_eq (LinearEquiv.refl R M).surjective (by simp)) =
        LinearEquiv.refl R _ := by
    rw [Submodule.Quotient.equiv_refl]
    exact LinearEquiv.toLinearMap_injective (Submodule.linearMap_qext _ (by ext; simp))
  refine LinearEquiv.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x φ =>
    rw [detLineCongr_tmul, hk, hc]
    simp
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- Transport along the composite of two commuting squares is the composite of the transports. -/
theorem detLineCongr_trans (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} {k : M'' →ₗ[R] N''} (e₁ : M ≃ₗ[R] M')
    (e₂ : N ≃ₗ[R] N') (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) (e₁' : M' ≃ₗ[R] M'')
    (e₂' : N' ≃ₗ[R] N'') (h' : k ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) :
    f.detLineCongr (e₁.trans e₁') (e₂.trans e₂') (comp_trans_eq_of_comp_eq h h') =
      (f.detLineCongr e₁ e₂ h).trans (g.detLineCongr e₁' e₂' h') := by
  have h'' := comp_trans_eq_of_comp_eq h h'
  have hk : (e₁.trans e₁').ofSubmodules _ _
      (f.map_ker_eq_ker_of_comp_eq (e₁.trans e₁').surjective (e₂.trans e₂').injective h'') =
      (e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)).trans
        (e₁'.ofSubmodules _ _ (g.map_ker_eq_ker_of_comp_eq e₁'.surjective e₂'.injective h')) := by
    ext x
    simp only [LinearEquiv.ofSubmodules_apply, LinearEquiv.trans_apply]
  have hc := Submodule.Quotient.equiv_trans _ _ _ e₂ e₂'
    (f.map_range_eq_range_of_comp_eq e₁.surjective h)
    (g.map_range_eq_range_of_comp_eq e₁'.surjective h')
    (f.map_range_eq_range_of_comp_eq (e₁.trans e₁').surjective h'')
  refine LinearEquiv.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x φ =>
    simp [hk, hc, comp_assoc]
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- Transport along the inverse of a commuting square is the inverse of the transport. -/
@[simp]
theorem detLineCongr_symm (f : M →ₗ[R] N) {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) :
    (f.detLineCongr e₁ e₂ h).symm = g.detLineCongr e₁.symm e₂.symm
      (by rw [LinearEquiv.comp_toLinearMap_symm_eq, comp_assoc, h,
        LinearEquiv.eq_toLinearMap_symm_comp]) := by
  refine LinearEquiv.ext fun z ↦ ?_
  rw [LinearEquiv.symm_apply_eq, ← LinearEquiv.trans_apply, ← detLineCongr_trans]
  simp

/-- Transport along a commuting square of automorphisms `e₁` of `M` and `e₂` of `N` multiplies the
determinant line of `f` by `det k₁ * (det k₂)⁻¹`, where `k₁` and `k₂` are the automorphisms that
`e₁` and `e₂` induce on the kernel and on the cokernel of `f`. -/
theorem detLineCongr_apply_eq_det_smul (f : M →ₗ[R] N) [Module.Free R (ker f)]
    [Module.Free R (N ⧸ range f)] {e₁ : M ≃ₗ[R] M} {e₂ : N ≃ₗ[R] N}
    (h : f ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) (z : f.detLine) :
    f.detLineCongr e₁ e₂ h z =
      (LinearEquiv.det
          (e₁.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)) *
        (LinearEquiv.det (Submodule.Quotient.equiv _ _ e₂
          (f.map_range_eq_range_of_comp_eq e₁.surjective h)))⁻¹) • z := by
  set k₂ := Submodule.Quotient.equiv _ _ e₂ (f.map_range_eq_range_of_comp_eq e₁.surjective h)
  induction z using TensorProduct.inductionOn with
  | tmul x φ =>
    -- The dual factor is precomposed with the inverse of multiplication by `det k₂`.
    have hφ : φ ∘ₗ (LinearEquiv.detLineCongr k₂).symm.toLinearMap =
        ((LinearEquiv.det k₂)⁻¹ : Rˣ) • φ := by
      refine LinearMap.ext fun y ↦ ?_
      have hy : (LinearEquiv.detLineCongr k₂).symm y = ((LinearEquiv.det k₂)⁻¹ : Rˣ) • y := by
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.detLineCongr_apply_eq_det_smul,
          ← LinearEquiv.coe_det, ← Units.smul_def, smul_inv_smul]
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hy, LinearMap.smul_apply, Units.smul_def,
        Units.smul_def, map_smul]
    rw [detLineCongr_tmul, LinearEquiv.detLineCongr_apply_eq_det_smul, hφ, ← LinearEquiv.coe_det]
    simp only [Units.smul_def, Units.val_mul, TensorProduct.smul_tmul_smul]
  | add a b ha hb => rw [map_add, ha, hb, smul_add]

/-- Let `e₁` and `e₂` act on the source and target of `f` as multiplication by the same unit `c`.
Transport along the commuting square they form multiplies the determinant line of `f` by
`c ^ ind f`, where `ind f = dim (ker f) - dim (coker f)` is the index of `f`. -/
theorem detLineCongr_apply_of_forall_eq_smul (f : M →ₗ[R] N) [Module.Free R (ker f)]
    [Module.Free R (N ⧸ range f)] {e₁ : M ≃ₗ[R] M} {e₂ : N ≃ₗ[R] N}
    (h : f ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) (c : Rˣ) (he₁ : ∀ x, e₁ x = c • x)
    (he₂ : ∀ y, e₂ y = c • y) (z : f.detLine) :
    f.detLineCongr e₁ e₂ h z =
      (c ^ ((finrank R (ker f) : ℤ) - finrank R (N ⧸ range f)) : Rˣ) • z := by
  -- Both induced automorphisms are multiplication by `c`, so their determinants are powers of `c`.
  rw [detLineCongr_apply_eq_det_smul,
    LinearEquiv.det_eq_pow_of_forall_eq_smul _ c fun x ↦ Subtype.ext (by simp [he₁]),
    LinearEquiv.det_eq_pow_of_forall_eq_smul _ c fun y ↦ ?_, zpow_sub, zpow_natCast, zpow_natCast]
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  simp [he₂]

/-- Negation of source and target multiplies the determinant line of `f` by
`(-1) ^ (dim (ker f) + dim (coker f))`, the sign of the parity of the index of `f`. -/
theorem detLineCongr_neg_apply (f : M →ₗ[R] N) [Module.Free R (ker f)]
    [Module.Free R (N ⧸ range f)] (z : f.detLine) :
    f.detLineCongr (LinearEquiv.neg R) (LinearEquiv.neg R) (by ext; simp) z =
      (-1 : R) ^ (finrank R (ker f) + finrank R (N ⧸ range f)) • z := by
  have h : ((-1 : Rˣ) ^ ((finrank R (ker f) : ℤ) - finrank R (N ⧸ range f))) =
      (-1) ^ (finrank R (ker f) + finrank R (N ⧸ range f)) := by
    rw [zpow_sub, zpow_natCast, zpow_natCast, ← inv_pow, inv_neg_one, ← pow_add]
  rw [detLineCongr_apply_of_forall_eq_smul f _ (-1) (fun x ↦ by simp) (fun y ↦ by simp), h,
    Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end CommRing

section Field

variable {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- The determinant line of a linear map with finite-dimensional kernel and cokernel is a line. -/
theorem finrank_detLine (f : M →ₗ[K] N) [FiniteDimensional K (ker f)]
    [FiniteDimensional K (N ⧸ range f)] : finrank K f.detLine = 1 := by
  rw [finrank_tensorProduct, Subspace.dual_finrank_eq, TauCeti.finrank_detLine,
    TauCeti.finrank_detLine]

end Field

end LinearMap

end

end
