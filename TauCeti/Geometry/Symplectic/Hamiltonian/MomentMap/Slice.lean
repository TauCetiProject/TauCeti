/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.LinearReduction
public import TauCeti.Geometry.Symplectic.Manifold.Invariants

/-!
# The symplectic slice at a point of a Hamiltonian action

Let `Z ↦ Z_M` be an infinitesimal action of a Lie algebra `𝔤` on a manifold `M` with a
nondegenerate two-form `σ`, and let `x ∈ M`. Write `W = 𝔤 · x` for the orbit tangent space
(`TauCeti.InfinitesimalAction.orbitTangent`), `𝔤_x` for the isotropy algebra and `W^σ` for the
`σ_x`-orthogonal of `W`. The restriction of `σ_x` to `W^σ` has kernel `W ∩ W^σ`, so it descends to
a symplectic form on the **symplectic slice**

`V = W^σ ⧸ (W ∩ W^σ)`

(`TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice`), the linear symplectic reduction of
`T_x M` along `W^σ` (`TauCeti.SymplecticForm.ReducedSpace`). It is the symplectic normal space of
the orbit through `x`, the linear part of the local normal form of Hamiltonian actions of Marle and
of Guillemin and Sternberg, in which a neighbourhood of the orbit is modelled on
`G ×_H (𝔪* × V)` for the stabilizer `H = G_x`.

The orbit map `Z ↦ Z_M(x)` identifies `𝔤 ⧸ 𝔤_x` with `W`
(`TauCeti.InfinitesimalAction.quotIsotropyEquivOrbitTangent`). If `μ` is a moment map whose cocycle
vanishes at `x`, as it does for a coadjoint-equivariant moment map of a Lie group action, then
`W^σ = ker dμ_x` and `dμ_x(Z_M(x)) = ⁅Z, μ(x)⁆`, so the orbit directions in `W^σ` are those of the
coadjoint stabilizer `𝔨 = 𝔤_{μ(x)}`:

`W ∩ W^σ = 𝔨 · x ≅ 𝔨 ⧸ 𝔤_x`

(`TauCeti.SmoothTwoForm.IsMomentMap.orbitTangent_inf_orthogonal` and
`TauCeti.SmoothTwoForm.IsMomentMap.quotEquivOrbitTangentInfOrthogonal`). Here `𝔤_x ≤ 𝔨`. Counting
dimensions, `dim V = dim M - dim 𝔤 - dim 𝔨 + 2 dim 𝔤_x`
(`TauCeti.SmoothTwoForm.IsMomentMap.finrank_symplecticSlice_add_finrank_add_finrank`). At a point
where the action is locally free this is the dimension of the reduced space `μ⁻¹(μ x) / G_{μ x}`.

For a smooth action of a Lie group `G` whose stabilizer `H = G_x` preserves `σ`, the tangent
representation `h ↦ dh_x` of `H` (`TauCeti.tangentRepresentation`) acts on `T_x M` by linear
symplectic maps of `σ_x` and preserves `W`, because `dh_x(ξ_M(x)) = (Ad_h ξ)_M(x)`
(`TauCeti.tangentRepresentation_mem_orbitTangent_fundamental`). Hence it preserves `W^σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.tangentRepresentation_mem_orthogonal_orbitTangent`), and
`H` acts on the symplectic slice by linear symplectomorphisms
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation`). Neither properness of the
action, compactness of `H`, closedness of `σ` nor a moment map is needed for this representation.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice hσ a x`: the symplectic slice
  `W^σ ⧸ (W ∩ W^σ)`, with its symplectic form
  `(hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal (a.orbitTangent x))`.
* `TauCeti.SmoothTwoForm.IsMomentMap.quotEquivOrbitTangentInfOrthogonal`: the identification
  `𝔨 ⧸ 𝔤_x ≃ W ∩ W^σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation`: the representation of
  the stabilizer of `x` on the symplectic slice.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice.mk_eq_mk_iff`: two vectors of `W^σ` have
  the same image in the slice exactly when they differ by an orbit direction.
* `TauCeti.SmoothTwoForm.IsMomentMap.orbitTangent_inf_orthogonal`: `W ∩ W^σ = 𝔨 · x`.
* `TauCeti.SmoothTwoForm.IsMomentMap.finrank_orbitTangent_inf_orthogonal_add_finrank_isotropy`:
  `dim (W ∩ W^σ) + dim 𝔤_x = dim 𝔨`.
* `TauCeti.SmoothTwoForm.IsMomentMap.finrank_symplecticSlice_add_finrank_add_finrank`:
  `dim V + dim 𝔤 + dim 𝔨 = dim M + 2 dim 𝔤_x`.
* `TauCeti.tangentRepresentation_mem_orbitTangent_fundamental`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.tangentRepresentation_mem_orthogonal_orbitTangent`: the
  stabilizer of `x` preserves the orbit tangent space `W` at `x` and its symplectic complement.
* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation_mk`: the stabilizer acts on
  the slice by `[u] ↦ [dh_x u]`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_symplecticSliceRepresentation`: the
  stabilizer acts on the slice by linear symplectomorphisms.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics* (Jerusalem, 1982), Math. Phys. Stud. 6, Reidel, 1984, 161–175.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 7.1 (the symplectic slice).
-/

public noncomputable section

open MulAction Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {x : M}

/-! ### The symplectic slice -/

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate) (a x)

/-- The **symplectic slice** of an infinitesimal action at `x`: the linear symplectic reduction
`W^σ ⧸ (W ∩ W^σ)` of `(T_x M, σ_x)` along the symplectic complement `W^σ` of the orbit tangent
space `W = 𝔤 · x`. Its symplectic form is
`(hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal (a.orbitTangent x))`,
`[u], [v] ↦ σ_x(u, v)`. -/
abbrev SymplecticSlice : Type _ :=
  (hσ.symplecticFormAt x).ReducedSpace ((hσ.symplecticFormAt x).orthogonal (a.orbitTangent x))

variable {hσ a x}

/-- Two vectors of `W^σ` have the same image in the symplectic slice exactly when they differ by
an orbit direction: the radical of `σ_x` on `W^σ` is `W ∩ W^σ`. -/
theorem SymplecticSlice.mk_eq_mk_iff [FiniteDimensional ℝ E]
    {u v : (hσ.symplecticFormAt x).orthogonal (a.orbitTangent x)} :
    (Submodule.Quotient.mk u : hσ.SymplecticSlice a x) = Submodule.Quotient.mk v ↔
      (u : TangentSpace I x) - v ∈ a.orbitTangent x := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [SymplecticForm.ReducedSpace.mk_eq_mk_iff, SymplecticForm.orthogonal_orthogonal]

end IsNondegenerate

/-! ### The radical of the symplectic slice for a moment map -/

namespace IsMomentMap

variable {μ : M → Module.Dual ℝ 𝔤} (h : σ.IsMomentMap a μ)

include h

/-- **The orbit directions orthogonal to the orbit are those of the coadjoint stabilizer.** Where
the cocycle of a moment map vanishes, `W ∩ W^σ = 𝔤_{μ(x)} · x` for the orbit tangent space
`W = 𝔤 · x`. -/
theorem orbitTangent_inf_orthogonal (hc : σ.momentCocycle a μ x = 0) :
    a.orbitTangent x ⊓ (σ.bilinFormAt x).orthogonal (a.orbitTangent x) =
      (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.map (a.eval x) := by
  rw [← h.ker_differential, h.orbitTangent_inf_ker_differential hc]

/-- Where the cocycle of a moment map vanishes, the orbit map `Z ↦ Z_M(x)` identifies
`𝔤_{μ(x)} ⧸ 𝔤_x` with `W ∩ W^σ`, for the orbit tangent space `W = 𝔤 · x`. -/
def quotEquivOrbitTangentInfOrthogonal (hc : σ.momentCocycle a μ x = 0) :
    ((lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule ⧸
        (a.isotropy x).toSubmodule.comap (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.subtype) ≃ₗ[ℝ]
      ↥(a.orbitTangent x ⊓ (σ.bilinFormAt x).orthogonal (a.orbitTangent x)) :=
  (a.quotIsotropyEquivMap x _).trans (LinearEquiv.ofEq _ _ (h.orbitTangent_inf_orthogonal hc).symm)

@[simp]
theorem coe_quotEquivOrbitTangentInfOrthogonal_mk (hc : σ.momentCocycle a μ x = 0)
    (Z : (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule) :
    (h.quotEquivOrbitTangentInfOrthogonal hc (Submodule.Quotient.mk Z) : TangentSpace I x) =
      a Z x := by
  rw [quotEquivOrbitTangentInfOrthogonal, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    InfinitesimalAction.coe_quotIsotropyEquivMap_mk]

/-- Where the cocycle of a moment map vanishes, `dim (W ∩ W^σ) + dim 𝔤_x = dim 𝔤_{μ(x)}` for the
orbit tangent space `W = 𝔤 · x`. -/
theorem finrank_orbitTangent_inf_orthogonal_add_finrank_isotropy [FiniteDimensional ℝ 𝔤]
    (hc : σ.momentCocycle a μ x = 0) :
    finrank ℝ ↥(a.orbitTangent x ⊓ (σ.bilinFormAt x).orthogonal (a.orbitTangent x)) +
      finrank ℝ (a.isotropy x) = finrank ℝ (lieAnnihilator ℝ 𝔤 (μ x)) := by
  have hle : (a.isotropy x).toSubmodule ≤ (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule :=
    h.isotropy_le_lieAnnihilator hc
  have h₁ := Submodule.finrank_quotient_add_finrank
    ((a.isotropy x).toSubmodule.comap (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.subtype)
  rw [(h.quotEquivOrbitTangentInfOrthogonal hc).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h₁
  exact h₁

/-- **The dimension of the symplectic slice.** For a nondegenerate form, where the cocycle of a
moment map vanishes, `dim V + dim 𝔤 + dim 𝔤_{μ(x)} = dim M + 2 dim 𝔤_x` for the symplectic slice
`V = W^σ ⧸ (W ∩ W^σ)`. At a locally free point, `dim V = dim M - dim 𝔤 - dim 𝔤_{μ(x)}`. -/
theorem finrank_symplecticSlice_add_finrank_add_finrank [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ 𝔤] (hσ : σ.IsNondegenerate) (hc : σ.momentCocycle a μ x = 0) :
    finrank ℝ (hσ.SymplecticSlice a x) + finrank ℝ 𝔤 + finrank ℝ (lieAnnihilator ℝ 𝔤 (μ x)) =
      finrank ℝ E + 2 * finrank ℝ (a.isotropy x) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have h₁ : finrank ℝ (hσ.SymplecticSlice a x) + finrank ℝ (a.orbitTangent x) +
      finrank ℝ ↥(a.orbitTangent x ⊓ (hσ.symplecticFormAt x).orthogonal (a.orbitTangent x)) =
        finrank ℝ E :=
    (hσ.symplecticFormAt x).finrank_reducedSpace_orthogonal_add (a.orbitTangent x)
  have h₂ := h.finrank_orbitTangent_inf_orthogonal_add_finrank_isotropy hc
  rw [← hσ.toBilinForm_symplecticFormAt, ← SymplecticForm.orthogonal_def] at h₂
  have h₃ := a.finrank_orbitTangent_add_finrank_isotropy x
  omega

end IsMomentMap

end SmoothTwoForm

/-! ### The stabilizer representation on the symplectic slice -/

section Representation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

/-- The tangent adjoint maps only need a `C¹` Lie group. -/
local instance : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- **The stabilizer preserves the orbit tangent space.** The tangent representation
`g ↦ dg_x` of the stabilizer of `x` maps the orbit tangent space `𝔤 · x` of the fundamental vector
fields into itself, since `dg_x` carries `ξ_M(x)` to `(Ad_g ξ)_M(x)`. -/
theorem tangentRepresentation_mem_orbitTangent_fundamental {x : M}
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x)
    (g : stabilizer G x) {v : TangentSpace I' x}
    (hv : v ∈ (InfinitesimalAction.fundamental I G I' M).orbitTangent x) :
    tangentRepresentation hd g v ∈ (InfinitesimalAction.fundamental I G I' M).orbitTangent x := by
  obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
  have h := (InfinitesimalAction.fundamental I G I' M).mem_orbitTangent x
    (Lie.adjointContinuousLinearMap (g : G) ξ)
  -- `dg_x ξ_M(x) = (Ad_g ξ)_M(g • x)`, read in `T_x M` through `g • x = x`.
  have key : tangentRepresentation hd g (fundamentalVectorField I' ξ x) =
      fundamentalVectorField I' (Lie.adjointContinuousLinearMap (g : G) ξ) x := by
    rw [tangentRepresentation_apply]
    exact (mfderiv_smul_fundamentalVectorField (g : G) ξ x).trans (congrArg
      (fun y ↦ (fundamentalVectorField I' (Lie.adjointContinuousLinearMap (g : G) ξ) y : E')) g.2)
  rw [InfinitesimalAction.fundamental_apply] at h ⊢
  rwa [key]

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I' M} {x : M}

omit [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [CompleteSpace E'] [IsManifold I' ∞ M] in
include I in
/-- Each element of the stabilizer of `x` acts by a map differentiable at `x`. -/
private theorem mdifferentiableAt_smul (x : M) :
    ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x := fun g _ ↦
  (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞) g).mdifferentiableAt
    (by simp)

include I in
/-- The tangent representation of the stabilizer of `x`, as linear automorphisms of `T_x M`. -/
private def tangentAut (x : M) : stabilizer G x →* TangentSpace I' x ≃ₗ[ℝ] TangentSpace I' x :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (TangentSpace I' x)).toMonoidHom.comp
    (tangentRepresentation (mdifferentiableAt_smul (I := I) x)).toRepresentation.asGroupHom

omit [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [CompleteSpace E'] [IsManifold I' ∞ M] in
include I in
private theorem tangentAut_apply
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x)
    (g : stabilizer G x) (v : TangentSpace I' x) :
    tangentAut (I := I) x g v = tangentRepresentation hd g v := by
  simp only [tangentAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Representation.asGroupHom_apply,
    ContRepresentation.toMonoidHom_apply]
  -- The two differentiability proofs agree by proof irrelevance.
  rfl

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate)
  (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)

include hσG

omit [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [CompleteSpace E'] in
private theorem isSymplectomorphism_tangentAut (g : stabilizer G x) :
    SymplecticForm.IsSymplectomorphism (hσ.symplecticFormAt x) (hσ.symplecticFormAt x)
      (tangentAut (I := I) x g) :=
  SymplecticForm.isSymplectomorphism_iff.2 fun u v ↦ by
    have hd := mdifferentiableAt_smul (I := I) (I' := I') (G := G) x
    rw [tangentAut_apply (I := I) hd, tangentAut_apply (I := I) hd]
    exact hσ.symplecticFormAt_tangentRepresentation (IG := I) hσG hd g u v

/-- **The stabilizer preserves the symplectic complement of the orbit.** If the stabilizer of `x`
preserves a nondegenerate two-form `σ`, its tangent representation `g ↦ dg_x` maps the
`σ_x`-orthogonal `W^σ` of the orbit tangent space `W` into itself. -/
theorem tangentRepresentation_mem_orthogonal_orbitTangent
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x)
    (g : stabilizer G x) {u : TangentSpace I' x}
    (hu : u ∈ (hσ.symplecticFormAt x).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)) :
    tangentRepresentation hd g u ∈ (hσ.symplecticFormAt x).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) := by
  refine SymplecticForm.mem_orthogonal_iff.2 fun w hw ↦ ?_
  -- Write `w = dg_x w'` with `w' = d(g⁻¹)_x w`, again an orbit direction, and use that `dg_x`
  -- preserves `σ_x`.
  have hw' := tangentRepresentation_mem_orbitTangent_fundamental hd g⁻¹ hw
  have hgw : tangentRepresentation hd g (tangentRepresentation hd g⁻¹ w) = w := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  rw [← hgw, hσ.symplecticFormAt_tangentRepresentation (IG := I) hσG hd g]
  exact SymplecticForm.mem_orthogonal_iff.1 hu _ hw'

/-- **The stabilizer representation on the symplectic slice.** If the stabilizer `H = G_x` of a
smooth Lie group action preserves a nondegenerate two-form `σ`, its tangent representation
`h ↦ dh_x` preserves `W^σ` and induces a representation of `H` on the symplectic slice
`W^σ ⧸ (W ∩ W^σ)`, `[u] ↦ [dh_x u]`, by linear symplectomorphisms
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_symplecticSliceRepresentation`). -/
def symplecticSliceRepresentation :
    stabilizer G x →*
      hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x ≃ₗ[ℝ]
        hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x :=
  (hσ.symplecticFormAt x).reducedSpaceRepresentation (tangentAut (I := I) x)
    (isSymplectomorphism_tangentAut hσ hσG) _ fun g u hu ↦ by
      have hd := mdifferentiableAt_smul (I := I) (I' := I') (G := G) x
      rw [tangentAut_apply (I := I) hd]
      exact hσ.tangentRepresentation_mem_orthogonal_orbitTangent hσG hd g hu

/-- The stabilizer acts on the symplectic slice by `[u] ↦ [dh_x u]`. -/
@[simp]
theorem symplecticSliceRepresentation_mk
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x)
    (g : stabilizer G x)
    (u : (hσ.symplecticFormAt x).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)) :
    hσ.symplecticSliceRepresentation hσG g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨tangentRepresentation hd g u,
        hσ.tangentRepresentation_mem_orthogonal_orbitTangent hσG hd g u.2⟩ := by
  rw [symplecticSliceRepresentation, SymplecticForm.reducedSpaceRepresentation_apply_mk]
  simp only [tangentAut_apply (I := I) hd]

/-- The stabilizer of `x` acts on the symplectic slice by linear symplectomorphisms of its reduced
symplectic form. -/
theorem isSymplectomorphism_symplecticSliceRepresentation (g : stabilizer G x) :
    SymplecticForm.IsSymplectomorphism
      ((hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)))
      ((hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)))
      (hσ.symplecticSliceRepresentation hσG g) :=
  SymplecticForm.isSymplectomorphism_reducedSpaceRepresentation _ _ _ _ g

end IsNondegenerate

end SmoothTwoForm

end Representation

end TauCeti
