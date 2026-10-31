/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Determinant lines of modules and of linear maps

The *determinant line* of a module `V` of rank `n` is its top exterior power `⋀ⁿ V`
(`TauCeti.detLine`). For a finite free module it is free of rank one. A linear isomorphism
`e : V ≃ W` induces an isomorphism of determinant lines sending `v₁ ∧ ⋯ ∧ vₙ` to
`e v₁ ∧ ⋯ ∧ e vₙ` (`TauCeti.detLineCongr`), functorially. A module of rank zero has determinant
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

## Main definitions

* `TauCeti.detLine R V`: the top exterior power `⋀[R]^(finrank R V) V`.
* `TauCeti.detLineCongr`: the isomorphism of determinant lines induced by `V ≃ₗ[R] W`.
* `TauCeti.detLineEquivOfFinrankEqZero`: the determinant line of a rank-zero module is `R`.
* `LinearMap.detLine f`: the determinant line `det (ker f) ⊗ (det (N ⧸ range f))^*` of `f`.
* `LinearMap.detLineEquivOfBijective`: the determinant line of a bijective map is `R`.
* `LinearMap.detLineCongr`: transport of determinant lines along a commuting square.

## Main results

* `TauCeti.finrank_detLine`: the determinant line of a finite free module has rank one.
* `TauCeti.detLineCongr_refl`, `TauCeti.detLineCongr_trans`, `TauCeti.detLineCongr_symm`: the
  induced isomorphisms are functorial.
* `LinearMap.finrank_detLine`: the determinant line of a linear map between vector spaces with
  finite-dimensional kernel and cokernel has dimension one.
* `LinearMap.map_ker_eq_ker_of_comp_eq` and `LinearMap.map_range_eq_range_of_comp_eq`: in a
  commuting square of linear maps whose horizontal sides are isomorphisms, these carry kernel onto
  kernel and range onto range.
* `LinearMap.detLineCongr_refl` and `LinearMap.detLineCongr_trans`: transport along commuting
  squares is functorial.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* D. Quillen, *Determinants of Cauchy–Riemann operators over a Riemann surface*,
  Funct. Anal. Appl. **19** (1985), 31–34.
-/

public section

noncomputable section

open Module TensorProduct

namespace exteriorPower

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- Exterior powers of equal degree are equal, and the identification renumbers the factors of an
exterior product. -/
theorem ofEq_ιMulti {n m : ℕ} (h : n = m) (v : Fin n → V) :
    LinearEquiv.ofEq _ _ (congrArg (⋀[R]^· V) h) (ιMulti R n v) =
      ιMulti R m (v ∘ Fin.cast h.symm) := by
  subst h
  rfl

end exteriorPower

namespace TauCeti

variable (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V]

/-- The **determinant line** of a module `V` of rank `n`: its top exterior power `⋀ⁿ V`. For a
finite free module it is free of rank one (`TauCeti.finrank_detLine`). -/
abbrev detLine : Type _ := ⋀[R]^(finrank R V) V

/-- The determinant line of a finite free module has rank one. -/
theorem finrank_detLine [Nontrivial R] [Module.Free R V] [Module.Finite R V] :
    finrank R (detLine R V) = 1 := by
  simp [detLine]

variable {R V} {W U : Type*} [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]

/-- The isomorphism of determinant lines `det V ≃ det W` induced by a linear isomorphism
`e : V ≃ W`. It sends `v₁ ∧ ⋯ ∧ vₙ` to `e v₁ ∧ ⋯ ∧ e vₙ` (`TauCeti.detLineCongr_ιMulti`). -/
def detLineCongr (e : V ≃ₗ[R] W) : detLine R V ≃ₗ[R] detLine R W :=
  (LinearEquiv.ofLinearMap (exteriorPower.map _ e.toLinearMap)
      (exteriorPower.map _ e.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp]; simp)
      (by rw [← exteriorPower.map_comp]; simp) :
      ⋀[R]^(finrank R V) V ≃ₗ[R] ⋀[R]^(finrank R V) W).trans
    (LinearEquiv.ofEq _ _ (congrArg (⋀[R]^· W) e.finrank_eq))

@[simp]
theorem detLineCongr_ιMulti (e : V ≃ₗ[R] W) (v : Fin (finrank R V) → V) :
    detLineCongr e (exteriorPower.ιMulti R _ v) =
      exteriorPower.ιMulti R _ (e ∘ v ∘ Fin.cast e.finrank_eq.symm) := by
  rw [detLineCongr, LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap,
    exteriorPower.map_apply_ιMulti, exteriorPower.ofEq_ιMulti e.finrank_eq]
  rfl

/-- Under the inclusion of the determinant line into the exterior algebra, `TauCeti.detLineCongr`
is the algebra map induced by `e`. -/
theorem coe_detLineCongr (e : V ≃ₗ[R] W) (x : detLine R V) :
    (detLineCongr e x : ExteriorAlgebra R W) = ExteriorAlgebra.map e.toLinearMap x := by
  simp only [detLineCongr, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.coe_ofLinearMap, exteriorPower.coe_map]

@[simp]
theorem detLineCongr_refl : detLineCongr (LinearEquiv.refl R V) = LinearEquiv.refl R _ := by
  ext x
  rw [coe_detLineCongr, LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id]
  rfl

@[simp]
theorem detLineCongr_trans (e : V ≃ₗ[R] W) (e' : W ≃ₗ[R] U) :
    detLineCongr (e.trans e') = (detLineCongr e).trans (detLineCongr e') := by
  ext x
  rw [LinearEquiv.trans_apply, coe_detLineCongr, coe_detLineCongr, coe_detLineCongr,
    LinearEquiv.coe_trans, ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply]

@[simp]
theorem detLineCongr_symm (e : V ≃ₗ[R] W) : (detLineCongr e).symm = detLineCongr e.symm := by
  refine LinearEquiv.ext fun x ↦ ?_
  rw [LinearEquiv.symm_apply_eq, ← LinearEquiv.trans_apply, ← detLineCongr_trans,
    LinearEquiv.symm_trans_self, detLineCongr_refl, LinearEquiv.refl_apply]

/-- The determinant line of a module of rank zero is `R`: the empty exterior product goes to `1`
(`TauCeti.detLineEquivOfFinrankEqZero_ιMulti`). -/
def detLineEquivOfFinrankEqZero (h : finrank R V = 0) : detLine R V ≃ₗ[R] R :=
  (LinearEquiv.ofEq _ _ (congrArg (⋀[R]^· V) h)).trans (exteriorPower.zeroEquiv R V)

@[simp]
theorem detLineEquivOfFinrankEqZero_ιMulti (h : finrank R V = 0) (v : Fin (finrank R V) → V) :
    detLineEquivOfFinrankEqZero h (exteriorPower.ιMulti R _ v) = 1 := by
  rw [detLineEquivOfFinrankEqZero, LinearEquiv.trans_apply, exteriorPower.ofEq_ιMulti h,
    exteriorPower.zeroEquiv_ιMulti]

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

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` with `e₁` and `e₂` linear isomorphisms, `e₁` carries the
kernel of `f` onto that of `g`. -/
theorem map_ker_eq_ker_of_comp_eq {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) :
    (ker f).map e₁.toLinearMap = ker g := by
  ext y
  have hy := LinearMap.congr_fun h (e₁.symm y)
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at hy
  rw [Submodule.mem_map_equiv, mem_ker, mem_ker, ← e₂.map_eq_zero_iff, ← hy]

/-- In a commuting square `g ∘ e₁ = e₂ ∘ f` with `e₁` and `e₂` linear isomorphisms, `e₂` carries the
range of `f` onto that of `g`. -/
theorem map_range_eq_range_of_comp_eq {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) :
    (range f).map e₂.toLinearMap = range g := by
  rw [← range_comp, ← h, range_comp, LinearEquiv.range, Submodule.map_top]

/-- The transport of determinant lines along a commuting square `g ∘ e₁ = e₂ ∘ f` of linear maps
with `e₁` and `e₂` linear isomorphisms. It is the tensor product of the isomorphism of kernel
determinant lines induced by `e₁` and the dual of the inverse of the isomorphism of cokernel
determinant lines induced by `e₂` (`LinearMap.detLineCongr_tmul`). -/
def detLineCongr {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) : f.detLine ≃ₗ[R] g.detLine :=
  TensorProduct.congr
    (TauCeti.detLineCongr (e₁.ofSubmodules _ _ (map_ker_eq_ker_of_comp_eq e₁ e₂ h)))
    (TauCeti.detLineCongr
      (Submodule.Quotient.equiv _ _ e₂ (map_range_eq_range_of_comp_eq e₁ e₂ h))).symm.dualMap

@[simp]
theorem detLineCongr_tmul {g : M' →ₗ[R] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) (x : TauCeti.detLine R (ker f))
    (φ : Dual R (TauCeti.detLine R (N ⧸ range f))) :
    detLineCongr e₁ e₂ h (x ⊗ₜ φ) =
      TauCeti.detLineCongr (e₁.ofSubmodules _ _ (map_ker_eq_ker_of_comp_eq e₁ e₂ h)) x ⊗ₜ
        (φ ∘ₗ (TauCeti.detLineCongr (Submodule.Quotient.equiv _ _ e₂
          (map_range_eq_range_of_comp_eq e₁ e₂ h))).symm.toLinearMap) :=
  (rfl)

/-- Transport along the identity square is the identity. -/
@[simp]
theorem detLineCongr_refl
    (h : f ∘ₗ (LinearEquiv.refl R M).toLinearMap = (LinearEquiv.refl R N).toLinearMap ∘ₗ f) :
    detLineCongr (LinearEquiv.refl R M) (LinearEquiv.refl R N) h = LinearEquiv.refl R _ := by
  have hk : (LinearEquiv.refl R M).ofSubmodules (ker f) (ker f)
      (map_ker_eq_ker_of_comp_eq (LinearEquiv.refl R M) (LinearEquiv.refl R N) h) =
        LinearEquiv.refl R _ := by
    ext; rfl
  have hc : Submodule.Quotient.equiv (range f) (range f) (LinearEquiv.refl R N)
      (map_range_eq_range_of_comp_eq (LinearEquiv.refl R M) (LinearEquiv.refl R N) h) =
        LinearEquiv.refl R _ := by
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl
  refine LinearEquiv.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x φ =>
    rw [detLineCongr_tmul, hk, hc]
    simp
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- Transport along the composite of two commuting squares is the composite of the transports. -/
theorem detLineCongr_trans {g : M' →ₗ[R] N'} {k : M'' →ₗ[R] N''} (e₁ : M ≃ₗ[R] M')
    (e₂ : N ≃ₗ[R] N') (h : g ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f) (e₁' : M' ≃ₗ[R] M'')
    (e₂' : N' ≃ₗ[R] N'') (h' : k ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g)
    (h'' : k ∘ₗ (e₁.trans e₁').toLinearMap = (e₂.trans e₂').toLinearMap ∘ₗ f) :
    detLineCongr (e₁.trans e₁') (e₂.trans e₂') h'' =
      (detLineCongr e₁ e₂ h).trans (detLineCongr e₁' e₂' h') := by
  have hk : (e₁.trans e₁').ofSubmodules _ _ (map_ker_eq_ker_of_comp_eq _ _ h'') =
      (e₁.ofSubmodules _ _ (map_ker_eq_ker_of_comp_eq _ _ h)).trans
        (e₁'.ofSubmodules _ _ (map_ker_eq_ker_of_comp_eq _ _ h')) := by
    ext; rfl
  have hc : Submodule.Quotient.equiv _ _ (e₂.trans e₂') (map_range_eq_range_of_comp_eq _ _ h'') =
      (Submodule.Quotient.equiv _ _ e₂ (map_range_eq_range_of_comp_eq _ _ h)).trans
        (Submodule.Quotient.equiv _ _ e₂' (map_range_eq_range_of_comp_eq _ _ h')) := by
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl
  refine LinearEquiv.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x φ =>
    rw [LinearEquiv.trans_apply, detLineCongr_tmul, detLineCongr_tmul, detLineCongr_tmul, hk, hc,
      TauCeti.detLineCongr_trans, TauCeti.detLineCongr_trans]
    rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add]

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
