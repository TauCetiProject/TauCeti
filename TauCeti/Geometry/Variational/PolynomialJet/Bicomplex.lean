/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Relative
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Mathlib.LinearAlgebra.TensorProduct.Tower
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The relative polynomial variational bicomplex

Over a commutative `R`-algebra `B` equipped with a family of base derivations
`δ : ι → Derivation R B B`, the **relative polynomial variational bicomplex**
`TauCeti.RelJetAlgebra.Bicomplex B ι α` is the exterior algebra
`ExteriorAlgebra (RelJetAlgebra B ι α) ((ι →₀ RelJetAlgebra B ι α) × Ω[RelJetAlgebra B ι α⁄B])`,
generated over `RelJetAlgebra B ι α` by horizontal one-forms `dx μ` and contact one-forms
`theta a I`.

## Main definitions

* `TauCeti.RelJetAlgebra.Bicomplex`: the exterior algebra of horizontal and contact forms.
* `TauCeti.RelJetAlgebra.Bicomplex.dx`, `TauCeti.RelJetAlgebra.Bicomplex.theta`: coordinate
  horizontal and contact one-forms.
* `TauCeti.RelJetAlgebra.Bicomplex.includeVert`, `TauCeti.RelJetAlgebra.Bicomplex.includeHoriz`:
  canonical inclusions of vertical forms and constant-coefficient horizontal forms.
* `TauCeti.RelJetAlgebra.Bicomplex.horizFirstWedge` and
  `TauCeti.RelJetAlgebra.Bicomplex.vertFirstWedge`: `R`-linear identifications of
  `VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)` with `Bicomplex B ι α` placing horizontal
  forms on the left (`β ∧ ω`) or on the right (`ω ∧ β`).
* `TauCeti.RelJetAlgebra.Bicomplex.dV` and `TauCeti.RelJetAlgebra.Bicomplex.dH`: the vertical and
  horizontal differentials.

## Main results

* `TauCeti.RelJetAlgebra.Bicomplex.horizFirstWedge_tmul_eq_neg_one_pow_smul_vertFirstWedge`:
  Koszul sign `(-1) ^ (p * q)` relating the two wedge orderings on bihomogeneous tensors.
* `TauCeti.RelJetAlgebra.Bicomplex.dV_dV`, `TauCeti.RelJetAlgebra.Bicomplex.dH_dH`,
  `TauCeti.RelJetAlgebra.Bicomplex.dH_dV_add_dV_dH`, and
  `TauCeti.RelJetAlgebra.Bicomplex.dH_add_dV_sq`: the variational bicomplex identities over any
  commutative ring `R` (without characteristic restrictions).
* `TauCeti.RelJetAlgebra.Bicomplex.dV_mul` and `TauCeti.RelJetAlgebra.Bicomplex.dH_mul`:
  graded Leibniz rules for `dV` and `dH`.
* `TauCeti.RelJetAlgebra.Bicomplex.dV_vertFirstWedge`,
  `TauCeti.RelJetAlgebra.Bicomplex.dH_vertFirstWedge_of_mem_exteriorPower`,
  `TauCeti.RelJetAlgebra.Bicomplex.dH_horizFirstWedge`, and
  `TauCeti.RelJetAlgebra.Bicomplex.dV_horizFirstWedge_of_mem_exteriorPower`: explicit sign
  comparisons between `(dH, dV)` and the unsigned double-differential complex
  `(horizDerivUnsigned, dAlgTensor)` under both wedge-ordering conventions.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, for horizontal and vertical
  differentials on jet spaces.
* R. E. Borcherds, *Quantum Field Theory* (lecture notes), for the comparison between the
  unsigned double-differential complex and the anticommuting variational bicomplex.
-/

public section

open ExteriorAlgebra KaehlerDifferential MvPolynomial TensorProduct

namespace TauCeti

namespace RelJetAlgebra

noncomputable section

/-- The algebra of forms in the relative polynomial variational bicomplex over `B`, generated over
`RelJetAlgebra B ι α` by horizontal one-forms `dx μ` and contact one-forms `theta a I`. -/
abbrev Bicomplex (B ι α : Type*) [CommRing B] :=
  ExteriorAlgebra (RelJetAlgebra B ι α)
    ((ι →₀ RelJetAlgebra B ι α) × Ω[RelJetAlgebra B ι α⁄B])

namespace Bicomplex

section Structure

variable (B ι α : Type*) [CommRing B]

/-- The horizontal coordinate one-form `dx^μ` in `Bicomplex B ι α`. -/
def dx (μ : ι) : Bicomplex B ι α :=
  ExteriorAlgebra.ι (RelJetAlgebra B ι α) (Finsupp.single μ (1 : RelJetAlgebra B ι α), 0)

/-- The contact coordinate one-form `θᵃ_I` in `Bicomplex B ι α`. -/
def theta (a : α) (I : ι →₀ ℕ) : Bicomplex B ι α :=
  ExteriorAlgebra.ι (RelJetAlgebra B ι α)
    (0, KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I)))

/-- Inclusion of vertical forms `VertForms B ι α` into `Bicomplex B ι α`. -/
def includeVert : VertForms B ι α →ₐ[RelJetAlgebra B ι α] Bicomplex B ι α :=
  ExteriorAlgebra.map
    (LinearMap.inr (RelJetAlgebra B ι α) (ι →₀ RelJetAlgebra B ι α) (Ω[RelJetAlgebra B ι α⁄B]))

/-- Inclusion of constant-coefficient horizontal forms `ExteriorAlgebra R (ι →₀ R)` into
`Bicomplex B ι α`. -/
def includeHoriz (R : Type*) [CommRing R] [Algebra R B] :
    ExteriorAlgebra R (ι →₀ R) →ₐ[R] Bicomplex B ι α :=
  ExteriorAlgebra.lift R
    ⟨(((ExteriorAlgebra.ι (RelJetAlgebra B ι α)).restrictScalars R).comp
        ((LinearMap.inl (RelJetAlgebra B ι α) (ι →₀ RelJetAlgebra B ι α)
          (Ω[RelJetAlgebra B ι α⁄B])).restrictScalars R)).comp
      (Finsupp.mapRange.linearMap (Algebra.linearMap R (RelJetAlgebra B ι α))),
      by intro _; exact ExteriorAlgebra.ι_sq_zero _⟩

variable {B ι α}

/-- Explicit exterior-generator formula for `dx B ι α μ`. -/
theorem dx_eq_ι (μ : ι) :
    dx B ι α μ =
      ExteriorAlgebra.ι (RelJetAlgebra B ι α)
        (Finsupp.single μ (1 : RelJetAlgebra B ι α), 0) := by
  rfl

/-- Explicit exterior-generator formula for `theta B ι α a I`. -/
theorem theta_eq_ι (a : α) (I : ι →₀ ℕ) :
    theta B ι α a I =
      ExteriorAlgebra.ι (RelJetAlgebra B ι α)
        (0, KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I))) := by
  rfl

/-- The grade involution negates `dx μ`. -/
@[simp]
theorem involute_dx (μ : ι) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
        (dx B ι α μ) =
      -(dx B ι α μ) := by
  rw [dx, CliffordAlgebra.involute_ι]

/-- The grade involution negates `theta a I`. -/
@[simp]
theorem involute_theta (a : α) (I : ι →₀ ℕ) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
        (theta B ι α a I) =
      -(theta B ι α a I) := by
  rw [theta, CliffordAlgebra.involute_ι]

/-- `includeVert` commutes with `algebraMap` from `RelJetAlgebra B ι α`. -/
theorem includeVert_algebraMap (p : RelJetAlgebra B ι α) :
    includeVert B ι α (algebraMap (RelJetAlgebra B ι α) (VertForms B ι α) p) =
      algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) p :=
  AlgHom.commutes _ p

/-- `includeVert` sends the vertical coordinate one-form `duᵃ_I` to `theta a I`. -/
@[simp]
theorem includeVert_ι_D_X (a : α) (I : ι →₀ ℕ) :
    includeVert B ι α
        (ExteriorAlgebra.ι (RelJetAlgebra B ι α)
          (KaehlerDifferential.D B (RelJetAlgebra B ι α) (X (a, I)))) =
      theta B ι α a I := by
  simp [includeVert, theta]

/-- Action of `includeHoriz` on a degree-one generator `ι R v`. -/
@[simp]
theorem includeHoriz_ι {R : Type*} [CommRing R] [Algebra R B] (v : ι →₀ R) :
    includeHoriz B ι α R (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι (RelJetAlgebra B ι α)
        (v.mapRange (algebraMap R (RelJetAlgebra B ι α)) (map_zero _), 0) := by
  unfold includeHoriz
  exact ExteriorAlgebra.lift_ι_apply R _ _ v

/-- `includeHoriz` sends the basis one-form `ι R (single μ 1)` to `dx μ`. -/
theorem includeHoriz_ι_single {R : Type*} [CommRing R] [Algebra R B] (μ : ι) :
    includeHoriz B ι α R (ExteriorAlgebra.ι R (Finsupp.single μ (1 : R))) = dx B ι α μ := by
  rw [includeHoriz_ι, Finsupp.mapRange_single, map_one, dx]

/-- `includeVert` commutes with the grade involution. -/
theorem includeVert_involute (ω : VertForms B ι α) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
        (includeVert B ι α ω) =
      includeVert B ι α
        (CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _)) ω) := by
  induction ω using CliffordAlgebra.induction with
  | algebraMap p => simp [AlgHom.commutes]
  | ι m => simp [includeVert]
  | mul x y hx hy => simp [map_mul, hx, hy]
  | add x y hx hy => simp [map_add, hx, hy]

/-- `includeHoriz` commutes with the grade involution. -/
theorem includeHoriz_involute {R : Type*} [CommRing R] [Algebra R B]
    (β : ExteriorAlgebra R (ι →₀ R)) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
        (includeHoriz B ι α R β) =
      includeHoriz B ι α R
        (CliffordAlgebra.involute (Q := (0 : QuadraticForm R _)) β) := by
  induction β using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (RelJetAlgebra B ι α), AlgHom.commutes,
      AlgHom.commutes, AlgHom.commutes, ← IsScalarTower.algebraMap_apply R (RelJetAlgebra B ι α)]
  | ι v => simp
  | mul x y hx hy => simp [map_mul, hx, hy]
  | add x y hx hy => simp [map_add, hx, hy]

/-- `includeVert` preserves exterior degree. -/
theorem includeVert_mem_exteriorPower {q : ℕ} {ω : VertForms B ι α}
    (hω : ω ∈ ⋀[RelJetAlgebra B ι α]^q (Ω[RelJetAlgebra B ι α⁄B])) :
    includeVert B ι α ω ∈
      ⋀[RelJetAlgebra B ι α]^q ((ι →₀ RelJetAlgebra B ι α) × Ω[RelJetAlgebra B ι α⁄B]) :=
  LinearMap.exteriorAlgebra_map_mem_exteriorPower _ hω

/-- `includeHoriz` preserves exterior degree. -/
theorem includeHoriz_mem_exteriorPower {R : Type*} [CommRing R] [Algebra R B] {p : ℕ}
    {β : ExteriorAlgebra R (ι →₀ R)} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    includeHoriz B ι α R β ∈
      ⋀[RelJetAlgebra B ι α]^p ((ι →₀ RelJetAlgebra B ι α) × Ω[RelJetAlgebra B ι α⁄B]) := by
  induction hβ using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one]
    exact ⟨algebraMap R (RelJetAlgebra B ι α) r,
      (IsScalarTower.algebraMap_apply R (RelJetAlgebra B ι α) (Bicomplex B ι α) r).symm⟩
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, includeHoriz_ι]
    exact TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower _ hx

/-- Auxiliary algebra equivalence induced by a linear equivalence on the underlying module. -/
private def exteriorMapEquiv {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    ExteriorAlgebra A M ≃ₐ[A] ExteriorAlgebra A N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
    (by ext m; simp) (by ext m; simp)

/-- Base-change identification `P ⊗[R] ExteriorAlgebra R (ι →₀ R) ≃ₐ[P] ExteriorAlgebra P (ι →₀ P)`
for `P = RelJetAlgebra B ι α`. -/
private def horizBaseChangeEquiv (R B ι α : Type*) [CommRing R] [CommRing B] [Algebra R B] :
    RelJetAlgebra B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R) ≃ₐ[RelJetAlgebra B ι α]
      ExteriorAlgebra (RelJetAlgebra B ι α) (ι →₀ RelJetAlgebra B ι α) :=
  (ExteriorAlgebra.baseChangeEquiv R (ι →₀ R) (RelJetAlgebra B ι α)).trans
    (exteriorMapEquiv (by
      classical
      exact TensorProduct.finsuppScalarRight R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α) ι))

private theorem map_inl_horizBaseChangeEquiv_one_tmul {R : Type*} [CommRing R] [Algebra R B]
    (β : ExteriorAlgebra R (ι →₀ R)) :
    ExteriorAlgebra.map
        (LinearMap.inl (RelJetAlgebra B ι α) (ι →₀ RelJetAlgebra B ι α)
          (Ω[RelJetAlgebra B ι α⁄B]))
        (horizBaseChangeEquiv R B ι α (1 ⊗ₜ[R] β)) =
      includeHoriz B ι α R β := by
  classical
  induction β using CliffordAlgebra.induction with
  | algebraMap r =>
    have h1 : (1 : RelJetAlgebra B ι α) ⊗ₜ[R] algebraMap R (ExteriorAlgebra R (ι →₀ R)) r =
        algebraMap (RelJetAlgebra B ι α) _ (algebraMap R (RelJetAlgebra B ι α) r) := by
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        Algebra.TensorProduct.one_def]
    rw [h1, AlgEquiv.commutes, AlgHom.commutes, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R (RelJetAlgebra B ι α)]
  | ι v =>
    have hv : (TensorProduct.finsuppScalarRight R (RelJetAlgebra B ι α) (RelJetAlgebra B ι α) ι)
        (1 ⊗ₜ[R] v) = v.mapRange (algebraMap R (RelJetAlgebra B ι α)) (map_zero _) := by
      refine Finsupp.ext fun j ↦ ?_
      simp only [TensorProduct.finsuppScalarRight_apply, Finsupp.mapRange_apply,
        LinearMap.lTensor_tmul, Finsupp.lapply_apply, AlgebraTensorModule.rid_tmul,
        Algebra.smul_def, mul_one]
    rw [horizBaseChangeEquiv, AlgEquiv.trans_apply, ExteriorAlgebra.baseChangeEquiv_apply,
      exteriorMapEquiv, AlgEquiv.ofAlgHom_apply, ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe,
      hv, ExteriorAlgebra.map_apply_ι, includeHoriz_ι]
    rfl
  | mul x y hx hy =>
    have hmul : (1 : RelJetAlgebra B ι α) ⊗ₜ[R] (x * y) =
        (1 ⊗ₜ[R] x) * (1 ⊗ₜ[R] y) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hmul, map_mul, map_mul, map_mul, hx, hy]
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy]

/-- Scalar-extension map `ExteriorAlgebra R (ι →₀ R) →ₐ[R] ExteriorAlgebra B (ι →₀ B)`. -/
def horizChangeRing (R B ι : Type*) [CommRing R] [CommRing B] [Algebra R B] :
    ExteriorAlgebra R (ι →₀ R) →ₐ[R] ExteriorAlgebra B (ι →₀ B) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι B).restrictScalars R).comp
        (Finsupp.mapRange.linearMap (Algebra.linearMap R B)),
      by intro _; exact ExteriorAlgebra.ι_sq_zero _⟩

/-- Action of `horizChangeRing` on a degree-one generator `ι R v`. -/
@[simp]
theorem horizChangeRing_ι {R : Type*} [CommRing R] [Algebra R B] (v : ι →₀ R) :
    horizChangeRing R B ι (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι B (v.mapRange (algebraMap R B) (map_zero _)) := by
  unfold horizChangeRing
  exact ExteriorAlgebra.lift_ι_apply R _ _ v

/-- `horizChangeRing` preserves exterior degree. -/
theorem horizChangeRing_mem_exteriorPower {R : Type*} [CommRing R] [Algebra R B] {p : ℕ}
    {β : ExteriorAlgebra R (ι →₀ R)} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    horizChangeRing R B ι β ∈ ⋀[B]^p (ι →₀ B) := by
  induction hβ using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one]
    exact ⟨algebraMap R B r,
      (IsScalarTower.algebraMap_apply R B (ExteriorAlgebra B (ι →₀ B)) r).symm⟩
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, horizChangeRing_ι]
    exact TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower _ hx

/-- `includeHoriz` factors through scalar extension `horizChangeRing R B ι`. -/
theorem includeHoriz_eq_base {R : Type*} [CommRing R] [Algebra R B]
    (β : ExteriorAlgebra R (ι →₀ R)) :
    includeHoriz B ι α R β = includeHoriz B ι α B (horizChangeRing R B ι β) := by
  induction β using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R B (ExteriorAlgebra B _),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply R B (Bicomplex B ι α)]
  | ι v =>
    rw [includeHoriz_ι, horizChangeRing_ι, includeHoriz_ι]
    congr 2
    refine Finsupp.ext fun μ ↦ ?_
    simp only [Finsupp.mapRange_apply, IsScalarTower.algebraMap_apply R B (RelJetAlgebra B ι α)]
  | mul x y hx hy => simp [map_mul, hx, hy]
  | add x y hx hy => simp [map_add, hx, hy]

variable (R B ι α : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- **Horizontal-first wedge isomorphism** `ω ⊗ₜ β ↦ β ∧ ω` identifying
`VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)` with `Bicomplex B ι α`. -/
def horizFirstWedge :
    VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R) ≃ₗ[R] Bicomplex B ι α :=
  let P := RelJetAlgebra B ι α
  let eP : VertForms B ι α ⊗[P] ExteriorAlgebra P (ι →₀ P) ≃ₗ[P] Bicomplex B ι α :=
    (TensorProduct.comm P (VertForms B ι α) (ExteriorAlgebra P (ι →₀ P))).trans
      ((GradedTensorProduct.of P (fun i ↦ ⋀[P]^i (ι →₀ P)) (fun j ↦ ⋀[P]^j (Ω[P⁄B]))).trans
        (ExteriorAlgebra.prodEquivTensor P (ι →₀ P) (Ω[P⁄B])).symm.toLinearEquiv)
  (AlgebraTensorModule.cancelBaseChange R P P (VertForms B ι α)
      (ExteriorAlgebra R (ι →₀ R))).symm.restrictScalars R
    |>.trans ((LinearEquiv.lTensor (VertForms B ι α)
      (horizBaseChangeEquiv R B ι α).toLinearEquiv).restrictScalars R)
    |>.trans (eP.restrictScalars R)

/-- **Vertical-first wedge isomorphism** `ω ⊗ₜ β ↦ ω ∧ β` identifying
`VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)` with `Bicomplex B ι α`. -/
def vertFirstWedge :
    VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R) ≃ₗ[R] Bicomplex B ι α :=
  let P := RelJetAlgebra B ι α
  let eP : VertForms B ι α ⊗[P] ExteriorAlgebra P (ι →₀ P) ≃ₗ[P] Bicomplex B ι α :=
    (GradedTensorProduct.of P (fun j ↦ ⋀[P]^j (Ω[P⁄B])) (fun i ↦ ⋀[P]^i (ι →₀ P))).trans
      ((ExteriorAlgebra.prodEquivTensor P (Ω[P⁄B]) (ι →₀ P)).symm.toLinearEquiv.trans
        (exteriorMapEquiv (LinearEquiv.prodComm P (Ω[P⁄B]) (ι →₀ P))).toLinearEquiv)
  (AlgebraTensorModule.cancelBaseChange R P P (VertForms B ι α)
      (ExteriorAlgebra R (ι →₀ R))).symm.restrictScalars R
    |>.trans ((LinearEquiv.lTensor (VertForms B ι α)
      (horizBaseChangeEquiv R B ι α).toLinearEquiv).restrictScalars R)
    |>.trans (eP.restrictScalars R)

variable {R B ι α}

/-- `horizFirstWedge` sends `ω ⊗ₜ β` to `includeHoriz R β * includeVert ω`. -/
@[simp]
theorem horizFirstWedge_tmul (ω : VertForms B ι α) (β : ExteriorAlgebra R (ι →₀ R)) :
    horizFirstWedge R B ι α (ω ⊗ₜ[R] β) =
      includeHoriz B ι α R β * includeVert B ι α ω := by
  change (ExteriorAlgebra.prodEquivTensor (RelJetAlgebra B ι α) _ _).symm
      (horizBaseChangeEquiv R B ι α (1 ⊗ₜ[R] β) ᵍ⊗ₜ[RelJetAlgebra B ι α] ω) = _
  rw [ExteriorAlgebra.prodEquivTensor_symm_tmul, map_inl_horizBaseChangeEquiv_one_tmul]
  rfl

/-- `vertFirstWedge` sends `ω ⊗ₜ β` to `includeVert ω * includeHoriz R β`. -/
@[simp]
theorem vertFirstWedge_tmul (ω : VertForms B ι α) (β : ExteriorAlgebra R (ι →₀ R)) :
    vertFirstWedge R B ι α (ω ⊗ₜ[R] β) =
      includeVert B ι α ω * includeHoriz B ι α R β := by
  change ExteriorAlgebra.map (LinearEquiv.prodComm (RelJetAlgebra B ι α) _ _).toLinearMap
      ((ExteriorAlgebra.prodEquivTensor (RelJetAlgebra B ι α) _ _).symm
        (ω ᵍ⊗ₜ[RelJetAlgebra B ι α] horizBaseChangeEquiv R B ι α (1 ⊗ₜ[R] β))) = _
  rw [ExteriorAlgebra.prodEquivTensor_symm_tmul, map_mul, ← AlgHom.comp_apply,
    ExteriorAlgebra.map_comp_map, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  have h1 : (LinearEquiv.prodComm (RelJetAlgebra B ι α)
      (Ω[RelJetAlgebra B ι α⁄B]) (ι →₀ RelJetAlgebra B ι α)).toLinearMap.comp
      (LinearMap.inl (RelJetAlgebra B ι α) (Ω[RelJetAlgebra B ι α⁄B])
        (ι →₀ RelJetAlgebra B ι α)) =
      LinearMap.inr (RelJetAlgebra B ι α) (ι →₀ RelJetAlgebra B ι α)
        (Ω[RelJetAlgebra B ι α⁄B]) :=
    LinearMap.ext fun _ ↦ rfl
  have h2 : (LinearEquiv.prodComm (RelJetAlgebra B ι α)
      (Ω[RelJetAlgebra B ι α⁄B]) (ι →₀ RelJetAlgebra B ι α)).toLinearMap.comp
      (LinearMap.inr (RelJetAlgebra B ι α) (Ω[RelJetAlgebra B ι α⁄B])
        (ι →₀ RelJetAlgebra B ι α)) =
      LinearMap.inl (RelJetAlgebra B ι α) (ι →₀ RelJetAlgebra B ι α)
        (Ω[RelJetAlgebra B ι α⁄B]) :=
    LinearMap.ext fun _ ↦ rfl
  rw [h1, h2, map_inl_horizBaseChangeEquiv_one_tmul]
  rfl

/-- Comparing horizontal-first and vertical-first wedge orderings on bihomogeneous pure tensors
picks up the Koszul sign `(-1) ^ (p * q)`. -/
theorem horizFirstWedge_tmul_eq_neg_one_pow_smul_vertFirstWedge {p q : ℕ}
    {ω : VertForms B ι α} {β : ExteriorAlgebra R (ι →₀ R)}
    (hω : ω ∈ ⋀[RelJetAlgebra B ι α]^q (Ω[RelJetAlgebra B ι α⁄B]))
    (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    horizFirstWedge R B ι α (ω ⊗ₜ[R] β) =
      (-1 : ℤ) ^ (p * q) • vertFirstWedge R B ι α (ω ⊗ₜ[R] β) := by
  rw [horizFirstWedge_tmul, vertFirstWedge_tmul,
    TauCeti.ExteriorAlgebra.mul_eq_neg_one_pow_smul_mul_of_mem
      (includeHoriz_mem_exteriorPower hβ) (includeVert_mem_exteriorPower hω),
    mul_comm q p, ← Int.cast_smul_eq_zsmul (RelJetAlgebra B ι α)]
  simp

end Structure

section Differentials

variable (B ι α : Type*) [CommRing B]

/-- **The vertical differential `d_V`** on `Bicomplex B ι α`, acting on vertical-first wedges
`ω ∧ β` as `(d_alg ω) ∧ β`. -/
def dV : Module.End B (Bicomplex B ι α) :=
  (vertFirstWedge B B ι α).conj (dAlgTensor B B ι α)

variable {B ι α}

/-- **Vertical-first comparison for `d_V`**: under `vertFirstWedge` (`ω ⊗ₜ β ↦ ω ∧ β`), `dV`
matches the unsigned vertical differential `dAlgTensor` with no sign. -/
theorem dV_vertFirstWedge {R : Type*} [CommRing R] [Algebra R B]
    (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dV B ι α (vertFirstWedge R B ι α x) =
      vertFirstWedge R B ι α (dAlgTensor R B ι α x) := by
  induction x using TensorProduct.inductionOn with
  | tmul ω β =>
    rw [vertFirstWedge_tmul, dAlgTensor_tmul, vertFirstWedge_tmul, includeHoriz_eq_base β,
      ← vertFirstWedge_tmul (R := B), dV, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, dAlgTensor_tmul, vertFirstWedge_tmul]
  | add x y hx hy => simp [hx, hy]

/-- `dV` squares to zero. -/
@[simp]
theorem dV_dV (ω : Bicomplex B ι α) : dV B ι α (dV B ι α ω) = 0 := by
  obtain ⟨u, rfl⟩ := (vertFirstWedge B B ι α).surjective ω
  rw [dV_vertFirstWedge, dV_vertFirstWedge, dAlgTensor_dAlgTensor, map_zero]

/-- On embedded vertical forms, `dV` restricts to `dAlg`. -/
@[simp]
theorem dV_includeVert (ω : VertForms B ι α) :
    dV B ι α (includeVert B ι α ω) = includeVert B ι α (dAlg B ι α ω) := by
  have h := dV_vertFirstWedge (R := B) (ω ⊗ₜ[B] (1 : ExteriorAlgebra B (ι →₀ B)))
  simpa using h

/-- `dV` annihilates constant-coefficient horizontal forms. -/
@[simp]
theorem dV_includeHoriz {R : Type*} [CommRing R] [Algebra R B]
    (β : ExteriorAlgebra R (ι →₀ R)) :
    dV B ι α (includeHoriz B ι α R β) = 0 := by
  have h := dV_vertFirstWedge (R := R) ((1 : VertForms B ι α) ⊗ₜ[R] β)
  simpa [MvPolynomialDeRham.d_one] using h

/-- On zero-forms `p : RelJetAlgebra B ι α`, `dV` acts by `includeVert (ι (D p))`. -/
@[simp]
theorem dV_algebraMap (p : RelJetAlgebra B ι α) :
    dV B ι α (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) p) =
      includeVert B ι α
        (ExteriorAlgebra.ι (RelJetAlgebra B ι α)
          (KaehlerDifferential.D B (RelJetAlgebra B ι α) p)) := by
  rw [← includeVert_algebraMap, dV_includeVert, MvPolynomialDeRham.d_algebraMap]

/-- `dV` annihilates base coefficients `C b`. -/
theorem dV_algebraMap_C (b : B) :
    dV B ι α (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) (C b)) = 0 := by
  rw [dV_algebraMap, ← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, map_zero]

/-- `dV` sends a field-jet coordinate `uᵃ_I` to the contact one-form `θᵃ_I`. -/
theorem dV_algebraMap_X (a : α) (I : ι →₀ ℕ) :
    dV B ι α (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) (X (a, I))) =
      theta B ι α a I := by
  rw [dV_algebraMap, includeVert_ι_D_X]

/-- `dV` annihilates horizontal coordinate one-forms `dx^μ`. -/
@[simp]
theorem dV_dx (μ : ι) : dV B ι α (dx B ι α μ) = 0 := by
  rw [← includeHoriz_ι_single (R := B), dV_includeHoriz]

/-- `dV` annihilates contact coordinate one-forms `θᵃ_I`. -/
@[simp]
theorem dV_theta (a : α) (I : ι →₀ ℕ) : dV B ι α (theta B ι α a I) = 0 := by
  rw [← includeVert_ι_D_X, dV_includeVert, MvPolynomialDeRham.d_ι_D_X, map_zero]

private theorem dV_includeVert_mul (ω : VertForms B ι α) (η : Bicomplex B ι α) :
    dV B ι α (includeVert B ι α ω * η) =
      includeVert B ι α (dAlg B ι α ω) * η +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
          (includeVert B ι α ω) * dV B ι α η := by
  obtain ⟨u, rfl⟩ := (vertFirstWedge B B ι α).surjective η
  induction u using TensorProduct.inductionOn with
  | tmul α' β =>
    rw [dV_vertFirstWedge, dAlgTensor_tmul, vertFirstWedge_tmul, vertFirstWedge_tmul, ← mul_assoc,
      ← map_mul, ← vertFirstWedge_tmul, dV_vertFirstWedge, dAlgTensor_tmul, vertFirstWedge_tmul,
      MvPolynomialDeRham.d_mul, map_add, add_mul, map_mul, map_mul, mul_assoc, mul_assoc,
      includeVert_involute]
  | add x y hx hy =>
    simp only [map_add, mul_add, hx, hy]
    abel

private theorem dV_includeHoriz_mul (β : ExteriorAlgebra B (ι →₀ B)) (η : Bicomplex B ι α) :
    dV B ι α (includeHoriz B ι α B β * η) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
        (includeHoriz B ι α B β) * dV B ι α η := by
  induction β using CliffordAlgebra.induction generalizing η with
  | algebraMap b =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B (RelJetAlgebra B ι α),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply B (RelJetAlgebra B ι α),
      ← Algebra.smul_def, map_smul, Algebra.smul_def]
  | ι v =>
    obtain ⟨u, rfl⟩ := (vertFirstWedge B B ι α).surjective η
    induction u using TensorProduct.inductionOn with
    | tmul ω γ =>
      rw [dV_vertFirstWedge, dAlgTensor_tmul, vertFirstWedge_tmul, vertFirstWedge_tmul, ← mul_assoc,
        includeHoriz_ι, ExteriorAlgebra.ι_mul_eq_involute_mul, includeVert_involute,
        ← includeHoriz_ι, mul_assoc, ← map_mul, ← vertFirstWedge_tmul, dV_vertFirstWedge,
        dAlgTensor_tmul, vertFirstWedge_tmul, MvPolynomialDeRham.d_involute, map_neg, neg_mul,
        map_mul, ← mul_assoc, ← includeVert_involute, includeHoriz_ι,
        ← ExteriorAlgebra.ι_mul_eq_involute_mul, mul_assoc, ← neg_mul,
        ← CliffordAlgebra.involute_ι, ← includeHoriz_ι]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  | mul x y hx hy =>
    rw [map_mul (includeHoriz B ι α B), mul_assoc, hx, hy, map_mul, mul_assoc]
  | add x y hx hy =>
    rw [map_add (includeHoriz B ι α B), add_mul, map_add, hx, hy, map_add, add_mul]

/-- **Graded Leibniz rule for `dV`**: `dV (ω * η) = dV ω * η + involute ω * dV η`. -/
theorem dV_mul (ω η : Bicomplex B ι α) :
    dV B ι α (ω * η) =
      dV B ι α ω * η +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _)) ω *
          dV B ι α η := by
  obtain ⟨u, rfl⟩ := (vertFirstWedge B B ι α).surjective ω
  induction u using TensorProduct.inductionOn with
  | tmul α' β =>
    rw [dV_vertFirstWedge, dAlgTensor_tmul, vertFirstWedge_tmul, vertFirstWedge_tmul, mul_assoc,
      dV_includeVert_mul, dV_includeHoriz_mul, ← mul_assoc, ← mul_assoc, ← map_mul]
  | add x y hx hy =>
    simp only [map_add, add_mul, hx, hy]
    abel

/-- **Horizontal-first sign comparison for `d_V`**: under `horizFirstWedge` (`ω ⊗ₜ β ↦ β ∧ ω`),
`dV` picks up the sign `(-1) ^ p` for `β` of horizontal degree `p`. -/
theorem dV_horizFirstWedge_of_mem_exteriorPower {R : Type*} [CommRing R] [Algebra R B]
    {p : ℕ} (ω : VertForms B ι α) {β : ExteriorAlgebra R (ι →₀ R)} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    dV B ι α (horizFirstWedge R B ι α (ω ⊗ₜ[R] β)) =
      (-1 : ℤ) ^ p • horizFirstWedge R B ι α (dAlgTensor R B ι α (ω ⊗ₜ[R] β)) := by
  rw [horizFirstWedge_tmul, dV_mul, dV_includeHoriz, zero_mul, zero_add, dV_includeVert,
    TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (includeHoriz_mem_exteriorPower hβ),
    smul_mul_assoc, dAlgTensor_tmul, horizFirstWedge_tmul,
    ← Int.cast_smul_eq_zsmul (RelJetAlgebra B ι α)]
  simp

section HorizontalDifferential

variable {R : Type*} [CommRing R] [Algebra R B] [Fintype ι]

/-- **The horizontal differential `d_H`** on `Bicomplex B ι α` induced by base derivations
`δ : ι → Derivation R B B`, acting on horizontal-first wedges `β ∧ ω` as
`∑ μ, (dx^μ ∧ β) ∧ (D_μ ω)`. -/
def dH (δ : ι → Derivation R B B) : Module.End R (Bicomplex B ι α) :=
  (horizFirstWedge R B ι α).conj (horizDerivUnsigned δ)

/-- **Horizontal-first comparison for `d_H`**: under `horizFirstWedge` (`ω ⊗ₜ β ↦ β ∧ ω`), `dH δ`
matches `horizDerivUnsigned δ` with no sign. -/
theorem dH_horizFirstWedge (δ : ι → Derivation R B B)
    (x : VertForms B ι α ⊗[R] ExteriorAlgebra R (ι →₀ R)) :
    dH δ (horizFirstWedge R B ι α x) =
      horizFirstWedge R B ι α (horizDerivUnsigned δ x) := by
  rw [dH, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- **Nilpotency of `d_H`**: `dH δ (dH δ ω) = 0` whenever the base derivations commute, over any
commutative ring `R`. -/
theorem dH_dH {δ : ι → Derivation R B B} (hδ : ∀ i j b, δ i (δ j b) = δ j (δ i b))
    (ω : Bicomplex B ι α) :
    dH δ (dH δ ω) = 0 := by
  obtain ⟨u, rfl⟩ := (horizFirstWedge R B ι α).surjective ω
  rw [dH_horizFirstWedge, dH_horizFirstWedge, horizDerivUnsigned_horizDerivUnsigned hδ, map_zero]

/-- On embedded vertical forms, `dH δ` acts by `∑ μ, dx^μ ∧ D_μ ω`. -/
@[simp]
theorem dH_includeVert (δ : ι → Derivation R B B) (ω : VertForms B ι α) :
    dH δ (includeVert B ι α ω) =
      ∑ μ : ι, dx B ι α μ * includeVert B ι α (totalDerivForm δ μ ω) := by
  have h := dH_horizFirstWedge δ (ω ⊗ₜ[R] (1 : ExteriorAlgebra R (ι →₀ R)))
  rw [horizFirstWedge_tmul, map_one, one_mul, horizDerivUnsigned_tmul, map_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [mul_one, horizFirstWedge_tmul, includeHoriz_ι_single]

/-- `dH δ` annihilates constant-coefficient horizontal forms. -/
@[simp]
theorem dH_includeHoriz (δ : ι → Derivation R B B) (β : ExteriorAlgebra R (ι →₀ R)) :
    dH δ (includeHoriz B ι α R β) = 0 := by
  have h := dH_horizFirstWedge δ ((1 : VertForms B ι α) ⊗ₜ[R] β)
  rw [horizFirstWedge_tmul, map_one, mul_one, horizDerivUnsigned_tmul, map_sum] at h
  rw [h]
  refine Finset.sum_eq_zero fun μ _ ↦ ?_
  rw [totalDerivForm_one, TensorProduct.zero_tmul, map_zero]

/-- On zero-forms `p : RelJetAlgebra B ι α`, `dH δ` acts by `∑ μ, (totalDeriv δ μ p) • dx^μ`. -/
@[simp]
theorem dH_algebraMap (δ : ι → Derivation R B B) (p : RelJetAlgebra B ι α) :
    dH δ (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) p) =
      ∑ μ : ι, totalDeriv δ μ p • dx B ι α μ := by
  rw [← includeVert_algebraMap, dH_includeVert]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [totalDerivForm_algebraMap, includeVert_algebraMap, ← Algebra.commutes, ← Algebra.smul_def]

/-- On base coefficients `C b`, `dH δ` acts by `∑ μ, C (δ μ b) • dx^μ`. -/
theorem dH_algebraMap_C (δ : ι → Derivation R B B) (b : B) :
    dH δ (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) (C b)) =
      ∑ μ : ι, (C (δ μ b) : RelJetAlgebra B ι α) • dx B ι α μ := by
  simp

/-- On field-jet coordinates `uᵃ_I`, `dH δ` acts by `∑ μ, uᵃ_(I+e_μ) • dx^μ`. -/
theorem dH_algebraMap_X (δ : ι → Derivation R B B) (a : α) (I : ι →₀ ℕ) :
    dH δ (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) (X (a, I))) =
      ∑ μ : ι, (X (a, I + Finsupp.single μ 1) : RelJetAlgebra B ι α) • dx B ι α μ := by
  simp

/-- `dH δ` annihilates horizontal coordinate one-forms `dx^μ`. -/
@[simp]
theorem dH_dx (δ : ι → Derivation R B B) (μ : ι) : dH δ (dx B ι α μ) = 0 := by
  rw [← includeHoriz_ι_single (R := R), dH_includeHoriz]

/-- On contact coordinate one-forms, `dH δ (θᵃ_I) = ∑ μ, dx^μ ∧ θᵃ_(I+e_μ)`. -/
@[simp]
theorem dH_theta (δ : ι → Derivation R B B) (a : α) (I : ι →₀ ℕ) :
    dH δ (theta B ι α a I) =
      ∑ μ : ι, dx B ι α μ * theta B ι α a (I + Finsupp.single μ 1) := by
  rw [← includeVert_ι_D_X, dH_includeVert]
  simp

private theorem dH_mul_includeVert (δ : ι → Derivation R B B) (ω : Bicomplex B ι α)
    (η : VertForms B ι α) :
    dH δ (ω * includeVert B ι α η) =
      dH δ ω * includeVert B ι α η +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _)) ω *
          dH δ (includeVert B ι α η) := by
  obtain ⟨u, rfl⟩ := (horizFirstWedge R B ι α).surjective ω
  induction u using TensorProduct.inductionOn with
  | tmul α' β =>
    rw [dH_horizFirstWedge, horizDerivUnsigned_tmul, map_sum, horizFirstWedge_tmul, mul_assoc,
      ← map_mul, ← horizFirstWedge_tmul, dH_horizFirstWedge, horizDerivUnsigned_tmul, map_sum,
      Finset.sum_mul, dH_includeVert, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [horizFirstWedge_tmul, horizFirstWedge_tmul, totalDerivForm_mul, map_add, mul_add,
      map_mul (includeVert B ι α), map_mul (includeVert B ι α)]
    congr 1
    · rw [mul_assoc]
    · rw [map_mul (includeHoriz B ι α R), includeHoriz_ι_single, mul_assoc (dx B ι α μ),
        ← mul_assoc (includeHoriz B ι α R β), ← mul_assoc (dx B ι α μ), dx,
        ExteriorAlgebra.ι_mul_eq_involute_mul, ← dx, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, add_mul, hx, hy]
    abel

private theorem dH_mul_includeHoriz (δ : ι → Derivation R B B) (ω : Bicomplex B ι α)
    (γ : ExteriorAlgebra R (ι →₀ R)) :
    dH δ (ω * includeHoriz B ι α R γ) = dH δ ω * includeHoriz B ι α R γ := by
  induction γ using CliffordAlgebra.induction generalizing ω with
  | algebraMap r =>
    rw [AlgHom.commutes, ← Algebra.commutes, ← Algebra.smul_def, map_smul, Algebra.smul_def,
      Algebra.commutes]
  | ι v =>
    obtain ⟨u, rfl⟩ := (horizFirstWedge R B ι α).surjective ω
    induction u using TensorProduct.inductionOn with
    | tmul α' β =>
      have hcomm (η : VertForms B ι α) :
          includeVert B ι α η * includeHoriz B ι α R (ExteriorAlgebra.ι R v) =
            includeHoriz B ι α R (ExteriorAlgebra.ι R v) *
              includeVert B ι α
                (CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _))
                  η) := by
        rw [includeHoriz_ι, ← includeVert_involute, ExteriorAlgebra.ι_mul_eq_involute_mul,
          CliffordAlgebra.involute_involute]
      rw [dH_horizFirstWedge, horizDerivUnsigned_tmul, map_sum, horizFirstWedge_tmul, mul_assoc,
        hcomm α', ← mul_assoc, ← map_mul, ← horizFirstWedge_tmul, dH_horizFirstWedge,
        horizDerivUnsigned_tmul, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [horizFirstWedge_tmul, horizFirstWedge_tmul, mul_assoc, hcomm,
        ← mul_assoc (ExteriorAlgebra.ι R _), map_mul (includeHoriz B ι α R), mul_assoc,
        totalDerivForm_involute]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | mul x y hx hy =>
    rw [map_mul (includeHoriz B ι α R), ← mul_assoc, hy, hx, mul_assoc]
  | add x y hx hy =>
    rw [map_add (includeHoriz B ι α R), mul_add, map_add, hx, hy, mul_add]

/-- **Graded Leibniz rule for `dH`**: `dH δ (ω * η) = dH δ ω * η + involute ω * dH δ η`. -/
theorem dH_mul (δ : ι → Derivation R B B) (ω η : Bicomplex B ι α) :
    dH δ (ω * η) =
      dH δ ω * η +
        CliffordAlgebra.involute (Q := (0 : QuadraticForm (RelJetAlgebra B ι α) _)) ω *
          dH δ η := by
  obtain ⟨u, rfl⟩ := (vertFirstWedge R B ι α).surjective η
  induction u using TensorProduct.inductionOn with
  | tmul α' γ =>
    rw [vertFirstWedge_tmul, ← mul_assoc, dH_mul_includeHoriz, dH_mul_includeVert, add_mul,
      mul_assoc, mul_assoc, ← dH_mul_includeHoriz]
  | add x y hx hy =>
    simp only [map_add, mul_add, hx, hy]
    abel

/-- **Vertical-first sign comparison for `d_H`**: under `vertFirstWedge` (`ω ⊗ₜ β ↦ ω ∧ β`),
`dH δ` picks up the sign `(-1) ^ q` for `ω` of vertical degree `q`. -/
theorem dH_vertFirstWedge_of_mem_exteriorPower (δ : ι → Derivation R B B) {q : ℕ}
    {ω : VertForms B ι α} (hω : ω ∈ ⋀[RelJetAlgebra B ι α]^q (Ω[RelJetAlgebra B ι α⁄B]))
    (β : ExteriorAlgebra R (ι →₀ R)) :
    dH δ (vertFirstWedge R B ι α (ω ⊗ₜ[R] β)) =
      (-1 : ℤ) ^ q • vertFirstWedge R B ι α (horizDerivUnsigned δ (ω ⊗ₜ[R] β)) := by
  rw [vertFirstWedge_tmul, dH_mul, dH_includeHoriz, mul_zero, add_zero, dH_includeVert,
    horizDerivUnsigned_tmul, map_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [vertFirstWedge_tmul, map_mul, includeHoriz_ι_single, ← mul_assoc, dx,
    ExteriorAlgebra.ι_mul_eq_involute_mul,
    TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower
      (includeVert_mem_exteriorPower (totalDerivForm_mem_exteriorPower δ μ hω)),
    smul_mul_assoc, smul_mul_assoc, ← Int.cast_smul_eq_zsmul (RelJetAlgebra B ι α)]
  simp

/-- **Anticommutation of `d_H` and `d_V`**: `dH δ (dV ω) + dV (dH δ ω) = 0` for every form `ω`
in `Bicomplex B ι α`, over any commutative ring `R`. -/
theorem dH_dV_add_dV_dH (δ : ι → Derivation R B B) (ω : Bicomplex B ι α) :
    dH δ (dV B ι α ω) + dV B ι α (dH δ ω) = 0 := by
  obtain ⟨u, rfl⟩ := (horizFirstWedge R B ι α).surjective ω
  induction u using TensorProduct.inductionOn with
  | tmul α' β =>
    induction β using DirectSum.Decomposition.inductionOn fun n ↦ ⋀[R]^n (ι →₀ R) with
    | zero => simp only [TensorProduct.tmul_zero, map_zero, add_zero]
    | @homogeneous p w =>
      obtain ⟨γ, hγ⟩ := w
      rw [dV_horizFirstWedge_of_mem_exteriorPower α' hγ, map_zsmul, dH_horizFirstWedge,
        dH_horizFirstWedge, horizDerivUnsigned_tmul, map_sum, map_sum]
      have hterm :
          ∑ μ : ι, dV B ι α
            (horizFirstWedge R B ι α
              (totalDerivForm δ μ α' ⊗ₜ[R]
                (ExteriorAlgebra.ι R (Finsupp.single μ (1 : R)) * γ))) =
          (-1 : ℤ) ^ (p + 1) •
            horizFirstWedge R B ι α (dAlgTensor R B ι α (horizDerivUnsigned δ (α' ⊗ₜ[R] γ))) := by
        rw [horizDerivUnsigned_tmul, map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun μ _ ↦ ?_
        exact dV_horizFirstWedge_of_mem_exteriorPower _
          (TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower _ hγ)
      rw [hterm, dAlgTensor_horizDerivUnsigned, ← add_smul, pow_succ, mul_neg_one, add_neg_cancel,
        zero_smul]
    | add w₁ w₂ ih₁ ih₂ =>
      simp only [TensorProduct.tmul_add, map_add]
      calc
        _ = (dH δ (dV B ι α (horizFirstWedge R B ι α (α' ⊗ₜ[R] w₁))) +
              dV B ι α (dH δ (horizFirstWedge R B ι α (α' ⊗ₜ[R] w₁)))) +
            (dH δ (dV B ι α (horizFirstWedge R B ι α (α' ⊗ₜ[R] w₂))) +
              dV B ι α (dH δ (horizFirstWedge R B ι α (α' ⊗ₜ[R] w₂)))) := by abel
        _ = 0 := by rw [ih₁, ih₂, add_zero]
  | add x y hx hy =>
    simp only [map_add]
    calc
      _ = (dH δ (dV B ι α (horizFirstWedge R B ι α x)) +
            dV B ι α (dH δ (horizFirstWedge R B ι α x))) +
          (dH δ (dV B ι α (horizFirstWedge R B ι α y)) +
            dV B ι α (dH δ (horizFirstWedge R B ι α y))) := by abel
      _ = 0 := by rw [hx, hy, add_zero]

/-- **Total differential squares to zero**: `(dH δ + dV)² = 0` whenever the base derivations
commute. -/
theorem dH_add_dV_sq {δ : ι → Derivation R B B}
    (hδ : ∀ i j b, δ i (δ j b) = δ j (δ i b)) (ω : Bicomplex B ι α) :
    ((dH δ + (dV B ι α).restrictScalars R : Module.End R (Bicomplex B ι α))
      ((dH δ + (dV B ι α).restrictScalars R : Module.End R (Bicomplex B ι α)) ω)) = 0 := by
  simp only [LinearMap.add_apply, LinearMap.coe_restrictScalars, map_add, dH_dH hδ, dV_dV,
    zero_add, add_zero]
  rw [add_comm]
  exact dH_dV_add_dV_dH δ ω

/-- Coordinate check: `dV (dH δ (uᵃ_I)) = - ∑ μ, dx^μ ∧ θᵃ_(I+e_μ)`. -/
theorem dV_dH_algebraMap_X (δ : ι → Derivation R B B) (a : α) (I : ι →₀ ℕ) :
    dV B ι α (dH δ (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) (X (a, I)))) =
      -(∑ μ : ι, dx B ι α μ * theta B ι α a (I + Finsupp.single μ 1)) := by
  have h := dH_dV_add_dV_dH δ (algebraMap (RelJetAlgebra B ι α) (Bicomplex B ι α) (X (a, I)))
  rw [dV_algebraMap_X, dH_theta] at h
  exact eq_neg_of_add_eq_zero_right h

end HorizontalDifferential

end Differentials

end Bicomplex

end

end RelJetAlgebra

end TauCeti
