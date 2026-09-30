/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# Equivalences of finite toric fans

An equivalence of finite fans is a compatible pair of equivalences of their integral lattices and
ambient real vector spaces which carries the cones of one fan exactly onto the cones of the other.
It induces an order isomorphism of the cone index types and a morphism in each direction.
Regularity and completeness are invariant under fan equivalence.

This is the combinatorial notion used to compare toric realizations without choosing coordinates.
In particular, the cone equivalence identifies the affine charts which are glued in the analytic
realization.

## Main declarations

* `TauCeti.Toric.FanEquiv`: an equivalence of finite fans.
* `TauCeti.Toric.FanEquiv.coneEquiv`: the induced order isomorphism of their cone index types.
* `TauCeti.Toric.FanEquiv.toFanHom`: the underlying morphism of fans.
* `TauCeti.Toric.FanEquiv.isRegular_iff`: regularity is invariant under fan equivalence.
* `TauCeti.Toric.FanEquiv.isComplete_iff`: completeness is invariant under fan equivalence.

## References

The definition follows §1.4 of W. Fulton, *Introduction to Toric Varieties*, and §3.3 of D. Cox,
J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {N N' N'' V V' V'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V']
  [Module ℝ V''] {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {Φ : Fan i} {Ψ : Fan i'} {Ω : Fan i''}

/-- An equivalence of finite fans consists of compatible equivalences of the integral lattices and
ambient real vector spaces which carry precisely the cones of the source fan to cones of the
target fan. -/
structure FanEquiv (Φ : Fan i) (Ψ : Fan i') where
  /-- The equivalence of integral lattices. -/
  latticeEquiv : N ≃+ N'
  /-- The equivalence of ambient real vector spaces. -/
  realEquiv : V ≃ₗ[ℝ] V'
  /-- The integral and real equivalences commute with the lattice embeddings. -/
  map_lattice : ∀ n, realEquiv (i n) = i' (latticeEquiv n)
  /-- A cone belongs to the target fan after transport exactly when it belongs to the source fan. -/
  map_mem : ∀ σ, PointedCone.map (realEquiv : V →ₗ[ℝ] V') σ ∈ Ψ.cones ↔ σ ∈ Φ.cones

namespace FanEquiv

/-- The real-linear part of a fan equivalence is determined by its integral part. -/
theorem realEquiv_toLinearMap_eq (e : FanEquiv Φ Ψ) :
    (e.realEquiv : V →ₗ[ℝ] V') = Φ.lattice.extend i' e.latticeEquiv :=
  Φ.lattice.eq_extend e.map_lattice

/-- Fan equivalences are determined by their equivalence of integral lattices. -/
@[ext]
theorem ext {e e' : FanEquiv Φ Ψ} (h : e.latticeEquiv = e'.latticeEquiv) : e = e' := by
  have hr : e.realEquiv = e'.realEquiv := by
    apply LinearEquiv.ext
    intro x
    exact DFunLike.congr_fun
      (e.realEquiv_toLinearMap_eq.trans (h ▸ e'.realEquiv_toLinearMap_eq.symm)) x
  cases e
  cases e'
  cases h
  cases hr
  rfl

/-- The identity equivalence of a fan. -/
protected def refl (Φ : Fan i) : FanEquiv Φ Φ where
  latticeEquiv := AddEquiv.refl N
  realEquiv := LinearEquiv.refl ℝ V
  map_lattice _ := rfl
  map_mem σ := by simp

/-- The integral part of the identity fan equivalence is the identity. -/
@[simp]
theorem refl_latticeEquiv (Φ : Fan i) :
    (FanEquiv.refl Φ).latticeEquiv = AddEquiv.refl N := (rfl)

/-- The real part of the identity fan equivalence is the identity. -/
@[simp]
theorem refl_realEquiv (Φ : Fan i) :
    (FanEquiv.refl Φ).realEquiv = LinearEquiv.refl ℝ V := (rfl)

/-- The inverse equivalence of finite fans. -/
protected def symm (e : FanEquiv Φ Ψ) : FanEquiv Ψ Φ where
  latticeEquiv := e.latticeEquiv.symm
  realEquiv := e.realEquiv.symm
  map_lattice n := by
    simpa using (congrArg e.realEquiv.symm (e.map_lattice (e.latticeEquiv.symm n))).symm
  map_mem τ := by
    have hcomp : (e.realEquiv : V →ₗ[ℝ] V').comp
        (e.realEquiv.symm : V' →ₗ[ℝ] V) = LinearMap.id := by
      ext x
      simp
    simpa only [PointedCone.map_map, hcomp, PointedCone.map_id] using
      (e.map_mem (PointedCone.map (e.realEquiv.symm : V' →ₗ[ℝ] V) τ)).symm

/-- The integral part of the inverse fan equivalence is the inverse integral equivalence. -/
@[simp]
theorem symm_latticeEquiv (e : FanEquiv Φ Ψ) :
    e.symm.latticeEquiv = e.latticeEquiv.symm := (rfl)

/-- The real part of the inverse fan equivalence is the inverse real equivalence. -/
@[simp]
theorem symm_realEquiv (e : FanEquiv Φ Ψ) :
    e.symm.realEquiv = e.realEquiv.symm := (rfl)

/-- The composite of two equivalences of finite fans. -/
def trans (e : FanEquiv Φ Ψ) (e' : FanEquiv Ψ Ω) : FanEquiv Φ Ω where
  latticeEquiv := e.latticeEquiv.trans e'.latticeEquiv
  realEquiv := e.realEquiv.trans e'.realEquiv
  map_lattice n := by simp [e.map_lattice, e'.map_lattice]
  map_mem σ := by
    rw [LinearEquiv.coe_trans, ← PointedCone.map_map]
    exact (e'.map_mem _).trans (e.map_mem σ)

/-- The integral part of a composite fan equivalence is the composite integral equivalence. -/
@[simp]
theorem trans_latticeEquiv (e : FanEquiv Φ Ψ) (e' : FanEquiv Ψ Ω) :
    (e.trans e').latticeEquiv = e.latticeEquiv.trans e'.latticeEquiv := (rfl)

/-- The real part of a composite fan equivalence is the composite real equivalence. -/
@[simp]
theorem trans_realEquiv (e : FanEquiv Φ Ψ) (e' : FanEquiv Ψ Ω) :
    (e.trans e').realEquiv = e.realEquiv.trans e'.realEquiv := (rfl)

/-- The identity fan equivalence is a left unit for composition. -/
@[simp]
theorem refl_trans (e : FanEquiv Φ Ψ) : (FanEquiv.refl Φ).trans e = e := by
  ext x
  rfl

/-- The identity fan equivalence is a right unit for composition. -/
@[simp]
theorem trans_refl (e : FanEquiv Φ Ψ) : e.trans (FanEquiv.refl Ψ) = e := by
  ext x
  rfl

/-- Composition of fan equivalences is associative. -/
theorem trans_assoc (e : FanEquiv Φ Ψ) (e' : FanEquiv Ψ Ω)
    {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V'''] [Module ℝ V''']
    {i''' : N''' →+ V'''} {Θ : Fan i'''} (e'' : FanEquiv Ω Θ) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') := by
  ext x
  rfl

/-- Inverting a fan equivalence twice gives the original equivalence. -/
@[simp]
theorem symm_symm (e : FanEquiv Φ Ψ) : e.symm.symm = e := by
  ext
  rfl

/-- The inverse of the identity fan equivalence is the identity. -/
@[simp]
theorem refl_symm (Φ : Fan i) : (FanEquiv.refl Φ).symm = FanEquiv.refl Φ := by
  ext
  rfl

/-- A fan equivalence followed by its inverse is the identity equivalence. -/
@[simp]
theorem self_trans_symm (e : FanEquiv Φ Ψ) : e.trans e.symm = FanEquiv.refl Φ := by
  ext x
  simp

/-- The inverse fan equivalence followed by the original is the identity equivalence. -/
@[simp]
theorem symm_trans_self (e : FanEquiv Φ Ψ) : e.symm.trans e = FanEquiv.refl Ψ := by
  ext x
  simp

private def coneMap (e : FanEquiv Φ Ψ) : Φ.cones → Ψ.cones := fun σ ↦
  ⟨PointedCone.map (e.realEquiv : V →ₗ[ℝ] V') σ.1, (e.map_mem σ.1).2 σ.2⟩

@[simp]
private theorem coneMap_coe (e : FanEquiv Φ Ψ) (σ : Φ.cones) :
    (e.coneMap σ : PointedCone ℝ V') =
      PointedCone.map (e.realEquiv : V →ₗ[ℝ] V') σ.1 :=
  (rfl)

/-- A fan equivalence induces an order isomorphism between the cones of its source and target.
In particular it preserves inclusions and intersections of cones (`OrderIso.map_inf`). -/
def coneEquiv (e : FanEquiv Φ Ψ) : Φ.cones ≃o Ψ.cones :=
  Equiv.toOrderIso
    { toFun := e.coneMap
      invFun := e.symm.coneMap
      left_inv σ := by
        apply Subtype.ext
        simp only [coneMap_coe, symm_realEquiv, PointedCone.map_map]
        convert PointedCone.map_id σ.1
        ext x
        simp
      right_inv τ := by
        apply Subtype.ext
        simp only [coneMap_coe, symm_realEquiv, PointedCone.map_map]
        convert PointedCone.map_id τ.1
        ext x
        simp }
    (fun _ _ ↦ Submodule.map_mono)
    (fun _ _ ↦ Submodule.map_mono)

/-- The induced cone equivalence transports a cone by the ambient linear equivalence. -/
@[simp]
theorem coneEquiv_apply_coe (e : FanEquiv Φ Ψ) (σ : Φ.cones) :
    (e.coneEquiv σ : PointedCone ℝ V') =
      PointedCone.map (e.realEquiv : V →ₗ[ℝ] V') σ.1 :=
  e.coneMap_coe σ

/-- The inverse induced cone equivalence is the cone equivalence of the inverse fan
equivalence. -/
@[simp]
theorem coneEquiv_symm (e : FanEquiv Φ Ψ) : e.coneEquiv.symm = e.symm.coneEquiv := (rfl)

/-- The cone equivalence of the identity fan equivalence is the identity. -/
@[simp]
theorem coneEquiv_refl (Φ : Fan i) : (FanEquiv.refl Φ).coneEquiv = OrderIso.refl Φ.cones := by
  ext σ
  simp

/-- The cone equivalence of a composite fan equivalence is the composite cone equivalence. -/
@[simp]
theorem coneEquiv_trans (e : FanEquiv Φ Ψ) (e' : FanEquiv Ψ Ω) :
    (e.trans e').coneEquiv = e.coneEquiv.trans e'.coneEquiv := by
  ext σ
  simp [PointedCone.map_map]

/-- The morphism of fans underlying a fan equivalence. -/
def toFanHom (e : FanEquiv Φ Ψ) : FanHom Φ Ψ where
  latticeMap := e.latticeEquiv
  realMap := e.realEquiv
  map_lattice := e.map_lattice
  map_cone σ hσ :=
    ⟨PointedCone.map (e.realEquiv : V →ₗ[ℝ] V') σ, (e.map_mem σ).2 hσ, le_rfl⟩

/-- The integral map of the underlying fan morphism is the integral equivalence. -/
@[simp]
theorem toFanHom_latticeMap (e : FanEquiv Φ Ψ) :
    e.toFanHom.latticeMap = e.latticeEquiv := (rfl)

/-- The real map of the underlying fan morphism is the ambient real equivalence. -/
@[simp]
theorem toFanHom_realMap (e : FanEquiv Φ Ψ) :
    e.toFanHom.realMap = e.realEquiv := (rfl)

/-- The underlying morphism of the identity fan equivalence is the identity morphism. -/
@[simp]
theorem toFanHom_refl (Φ : Fan i) : (FanEquiv.refl Φ).toFanHom = FanHom.id Φ := by
  ext x
  simp

/-- The underlying morphism respects composition of fan equivalences. -/
@[simp]
theorem toFanHom_trans (e : FanEquiv Φ Ψ) (e' : FanEquiv Ψ Ω) :
    (e.trans e').toFanHom = e'.toFanHom.comp e.toFanHom := by
  ext x
  simp

/-- The least target cone of the underlying fan morphism is the image cone itself. -/
@[simp]
theorem toFanHom_leastCone (e : FanEquiv Φ Ψ) (σ : Φ.cones) :
    e.toFanHom.leastCone σ.2 = e.coneEquiv σ := by
  apply le_antisymm
  · exact e.toFanHom.leastCone_le σ.2 (e.coneEquiv σ).2 le_rfl
  · exact e.toFanHom.map_le_leastCone σ.2

/-- A finite fan is regular exactly when an equivalent fan is regular. -/
theorem isRegular_iff (e : FanEquiv Φ Ψ) : Ψ.IsRegular ↔ Φ.IsRegular := by
  constructor
  · intro hΨ
    rw [Fan.isRegular_iff] at hΨ ⊢
    intro σ hσ
    exact (isRegularCone_map_equiv_iff e.map_lattice).1
      (hΨ _ ((e.map_mem σ).2 hσ))
  · intro hΦ
    rw [Fan.isRegular_iff] at hΦ ⊢
    intro τ hτ
    exact (isRegularCone_map_equiv_iff e.symm.map_lattice).1
      (hΦ _ ((e.symm.map_mem τ).2 hτ))

/-- The ambient linear equivalence carries the support of the source fan onto the support of the
target fan. -/
theorem image_support (e : FanEquiv Φ Ψ) : e.realEquiv '' Φ.support = Ψ.support := by
  refine subset_antisymm e.toFanHom.mapsTo_support.image_subset fun x hx ↦ ?_
  exact ⟨e.realEquiv.symm x, e.symm.toFanHom.mapsTo_support hx, e.realEquiv.apply_symm_apply x⟩

/-- Completeness of finite fans is invariant under fan equivalence. -/
theorem isComplete_iff (e : FanEquiv Φ Ψ) : Ψ.IsComplete ↔ Φ.IsComplete := by
  rw [Fan.isComplete_iff, Fan.isComplete_iff]
  constructor
  · intro h x
    have hx : e.realEquiv x ∈ e.realEquiv '' Φ.support := by
      rw [e.image_support]
      exact Ψ.mem_support.2 (h _)
    obtain ⟨y, hy, hyx⟩ := hx
    exact Φ.mem_support.1 (e.realEquiv.injective hyx ▸ hy)
  · intro h x
    apply Ψ.mem_support.1
    rw [← e.image_support]
    exact ⟨e.realEquiv.symm x, Φ.mem_support.2 (h _), e.realEquiv.apply_symm_apply x⟩

end FanEquiv

end TauCeti.Toric
