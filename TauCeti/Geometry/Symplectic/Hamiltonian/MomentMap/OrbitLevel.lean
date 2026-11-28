/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RegularLevel

/-!
# Preimages of coadjoint orbits under a moment map are coisotropic

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a Lie algebra `𝔤` on a
manifold `M` with a two-form `σ`, in the convention `ι_{Z_M} σ = d⟨μ, Z⟩`
(`TauCeti.SmoothTwoForm.IsMomentMap`), and let `x ∈ M` be a point at which the cocycle of `μ`
vanishes, as it does everywhere for a coadjoint-equivariant moment map of a Lie group action
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`). Write `c = μ(x)`,
`𝔤 · c = {⁅Z, c⁆}` for the tangent space of its coadjoint orbit `O`
(`Module.Dual.coadjointTangentMap`) and `𝔤_c` for its coadjoint stabilizer.

A level `μ⁻¹(c)` is coisotropic only when `c` is coadjoint-fixed
(`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropic_ker_differential_iff`). The preimage `μ⁻¹(O)` of
the whole coadjoint orbit, on the other hand, is coisotropic wherever `σ` is nondegenerate and the
cocycle of `μ` vanishes (for instance everywhere, for a coadjoint-equivariant moment map of a Lie
group action and a symplectic form). This file proves the pointwise statement, at the level of
tangent spaces:

* `dμ_x` maps the orbit tangent space `𝔤 · x` onto `𝔤 · c`, since `dμ_x(Z_M x) = ⁅Z, c⁆`
  (`TauCeti.SmoothTwoForm.IsMomentMap.map_differential_orbitTangent`). Hence the tangent space
  `dμ_x⁻¹(𝔤 · c)` of `μ⁻¹(O)`, when `μ` is transverse to `O`, is `ker dμ_x + 𝔤 · x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.comap_differential_range_coadjointTangentMap`).
* Where `σ_x` is nondegenerate, the symplectic complement of `ker dμ_x + 𝔤 · x` is
  `(𝔤 · x)^σ ∩ (ker dμ_x)^σ = ker dμ_x ∩ 𝔤 · x = 𝔤_c · x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.orthogonal_ker_differential_sup_orbitTangent`). It lies in
  `𝔤 · x`, so `ker dμ_x + 𝔤 · x` is coisotropic
  (`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropic_ker_differential_sup_orbitTangent`), and its
  null directions are the stabilizer directions `𝔤_c · x`, as for the level itself
  (`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_sup_orbitTangent_inf_orthogonal`).
* Where moreover the action is locally free, `ker dμ_x + 𝔤 · x` has dimension `dim M - dim 𝔤_c`
  (`TauCeti.SmoothTwoForm.IsMomentMap.finrank_ker_differential_sup_orbitTangent_add_finrank`), the
  dimension of `μ⁻¹(O)`: the level `μ⁻¹(c)` of dimension `dim M - dim 𝔤` thickened by the
  `dim 𝔤 - dim 𝔤_c` directions of `O`.

Consequently every map `g : N → M` whose tangent images are the subspaces `dμ⁻¹(𝔤 · μ(g p))`, such
as a parametrization of `μ⁻¹(O)`, is a coisotropic map
(`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropicMap_of_range_mfderiv_eq`). This is the
coisotropicness of the orbit-level manifold in the shifting trick, which realizes the reduced space
at `c` as the reduced space at zero of the shifted moment map `(x, o) ↦ μ(x) - o` on `M × O⁻`.

These subspaces are also described through a map `ι : N → 𝔤*` whose tangent images are the orbit
tangent spaces `𝔤 · ι(n)`, such as a parametrization of `O`: where `μ(x) = ι(n)`, `dμ_x(v)` lies in
the tangent image of `ι` at `n` exactly when `v` lies in `dμ_x⁻¹(𝔤 · μ(x))`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_mfderiv_components_eq_iff`).

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting trick).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  (h : σ.IsMomentMap a μ) {x : M}

include h

/-! ### The tangent space of the preimage of a coadjoint orbit -/

/-- **A moment map sends orbit directions to coadjoint orbit directions.** Where the cocycle of a
moment map vanishes, `dμ_x` maps the orbit tangent space `𝔤 · x` onto the tangent space
`𝔤 · μ(x) = {⁅Z, μ(x)⁆}` of the coadjoint orbit of `μ(x)`. -/
theorem map_differential_orbitTangent (hc : σ.momentCocycle a μ x = 0) :
    (a.orbitTangent x).map (h.differential x) = LinearMap.range (μ x).coadjointTangentMap := by
  ext ν
  simp only [Submodule.mem_map, InfinitesimalAction.mem_orbitTangent_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨Z, rfl⟩, rfl⟩
    exact ⟨Submodule.Quotient.mk Z, by
      rw [Module.Dual.coadjointTangentMap_mk, h.differential_apply_of_momentCocycle_eq_zero hc]⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    exact ⟨a Z x, ⟨Z, rfl⟩, by
      rw [Module.Dual.coadjointTangentMap_mk, h.differential_apply_of_momentCocycle_eq_zero hc]⟩

/-- **The tangent space of the preimage of a coadjoint orbit.** Where the cocycle of a moment map
vanishes, the vectors that `dμ_x` sends into the tangent space `𝔤 · μ(x)` of the coadjoint orbit
of `μ(x)` are `ker dμ_x + 𝔤 · x`. When `μ` is transverse to the orbit, this is the tangent space at
`x` of its preimage. -/
theorem comap_differential_range_coadjointTangentMap (hc : σ.momentCocycle a μ x = 0) :
    (LinearMap.range (μ x).coadjointTangentMap).comap (h.differential x) =
      LinearMap.ker (h.differential x) ⊔ a.orbitTangent x := by
  rw [← h.map_differential_orbitTangent hc, Submodule.comap_map_eq, sup_comm]

/-! ### Coisotropicness -/

/-- **The symplectic complement of the preimage of a coadjoint orbit.** Where the form is
nondegenerate and the cocycle of a moment map vanishes, the `σ_x`-orthogonal of
`ker dμ_x + 𝔤 · x` is the space `𝔤_{μ(x)} · x` of stabilizer directions. -/
theorem orthogonal_ker_differential_sup_orbitTangent [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0) :
    (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x) ⊔ a.orbitTangent x) =
      (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.map (a.eval x) := by
  have hsup : (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x)) ⊓
      (σ.bilinFormAt x).orthogonal (a.orbitTangent x) =
        (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x) ⊔ a.orbitTangent x) :=
    (Submodule.orthogonalBilin_sup (B := σ.bilinFormAt x) _ _).symm
  rw [← hsup, h.orthogonal_ker_differential hσx, ← h.ker_differential,
    h.orbitTangent_inf_ker_differential hc]

/-- The stabilizer directions `𝔤_{μ(x)} · x` are orbit directions, so they lie in
`ker dμ_x + 𝔤 · x`. -/
private theorem map_lieAnnihilator_le_ker_differential_sup_orbitTangent :
    (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.map (a.eval x) ≤
      LinearMap.ker (h.differential x) ⊔ a.orbitTangent x :=
  (LinearMap.map_le_range (f := a.eval x)).trans ((a.orbitTangent_eq_range x).ge.trans le_sup_right)

/-- **The null directions on the preimage of a coadjoint orbit are the stabilizer directions.**
Where the form is nondegenerate and the cocycle of a moment map vanishes, the kernel of `σ_x`
restricted to `ker dμ_x + 𝔤 · x` is `𝔤_{μ(x)} · x`, the same as on the level `ker dμ_x`
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_inf_orthogonal`). -/
theorem ker_differential_sup_orbitTangent_inf_orthogonal [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0) :
    (LinearMap.ker (h.differential x) ⊔ a.orbitTangent x) ⊓
        (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x) ⊔ a.orbitTangent x) =
      (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.map (a.eval x) := by
  rw [h.orthogonal_ker_differential_sup_orbitTangent hσx hc]
  exact inf_eq_right.2 h.map_lieAnnihilator_le_ker_differential_sup_orbitTangent

/-- **The preimage of a coadjoint orbit is coisotropic.** For a nondegenerate form, where the
cocycle of a moment map vanishes, `ker dμ_x + 𝔤 · x` is coisotropic, whether or not `μ(x)` is
coadjoint-fixed. -/
theorem isCoisotropic_ker_differential_sup_orbitTangent [FiniteDimensional ℝ E]
    (hσ : σ.IsNondegenerate) (hc : σ.momentCocycle a μ x = 0) :
    (hσ.symplecticFormAt x).IsCoisotropic
      (LinearMap.ker (h.differential x) ⊔ a.orbitTangent x) := by
  rw [SymplecticForm.isCoisotropic_iff_le, SymplecticForm.orthogonal_def,
    hσ.toBilinForm_symplecticFormAt,
    h.orthogonal_ker_differential_sup_orbitTangent (hσ.nondegenerate_bilinFormAt x) hc]
  exact h.map_lieAnnihilator_le_ker_differential_sup_orbitTangent

/-- **The dimension of the preimage of a coadjoint orbit.** Where the form is nondegenerate, the
cocycle of a moment map vanishes and the action is locally free, `ker dμ_x + 𝔤 · x` has dimension
`dim M - dim 𝔤_{μ(x)}`. -/
theorem finrank_ker_differential_sup_orbitTangent_add_finrank [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0)
    (hfree : a.isotropy x = ⊥) :
    finrank ℝ ↥(LinearMap.ker (h.differential x) ⊔ a.orbitTangent x) +
        finrank ℝ (lieAnnihilator ℝ 𝔤 (μ x)) = finrank ℝ E := by
  have hinf : finrank ℝ ↥(a.orbitTangent x ⊓ LinearMap.ker (h.differential x)) =
      finrank ℝ (lieAnnihilator ℝ 𝔤 (μ x)) := by
    rw [h.orbitTangent_inf_ker_differential hc]
    exact (Submodule.equivMapOfInjective _ ((a.isotropy_eq_bot_iff x).1 hfree) _).finrank_eq.symm
  have hsum := h.finrank_ker_differential_add_finrank_orbitTangent hσx
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (a.orbitTangent x)
    (LinearMap.ker (h.differential x))
  rw [finrank_tangentSpace] at hsum
  rw [sup_comm, ← hinf]
  omega

/-! ### Parametrizations of the preimage of a coadjoint orbit -/

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Parametrizations of the preimage of a coadjoint orbit are coisotropic.** For a nondegenerate
form, let `g : N → M` be a map at whose points the cocycle of a moment map vanishes and whose
tangent image at each `p` is the space `dμ⁻¹(𝔤 · μ(g p))` of vectors that `dμ` sends into the
tangent space of the coadjoint orbit of `μ(g p)`. Then `g` is a coisotropic map. -/
theorem isCoisotropicMap_of_range_mfderiv_eq [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate)
    {g : N → M} (hc : ∀ p, σ.momentCocycle a μ (g p) = 0)
    (hg : ∀ p, LinearMap.range (mfderiv J I g p).toLinearMap =
      (LinearMap.range (μ (g p)).coadjointTangentMap).comap (h.differential (g p))) :
    hσ.IsCoisotropicMap J g := IsNondegenerate.isCoisotropicMap_iff.2 fun p ↦ by
  rw [hg p, h.comap_differential_range_coadjointTangentMap (hc p)]
  exact h.isCoisotropic_ker_differential_sup_orbitTangent hσ (hc p)

/-- **The vectors that `dμ` sends into a coadjoint orbit.** At a point `x` with `μ(x) = ι(n)`, if
the tangent image of `ι` at `n` consists of the coordinates of the tangent space `𝔤 · ι(n)` of the
coadjoint orbit, then `dμ_x(v)` lies in the tangent image of `ι` at `n`, both read in a basis of
`𝔤`, exactly when `dμ_x(v)` lies in `𝔤 · μ(x)`. -/
theorem exists_mfderiv_components_eq_iff {κ : Type*} [Fintype κ] (b : Basis κ ℝ 𝔤)
    {ι : N → Module.Dual ℝ 𝔤} {n : N} (hxn : μ x = ι n)
    (hιT : Set.range (mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) =
      Set.range fun Z : 𝔤 ↦ fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ 𝔤) (b i))
    (v : TangentSpace I x) :
    (∃ w : TangentSpace J n, mfderiv I 𝓘(ℝ, κ → ℝ) (fun y i ↦ μ y (b i)) x v =
        mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n w) ↔
      v ∈ (LinearMap.range (μ x).coadjointTangentMap).comap (h.differential x) := by
  simp only [Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨Z, hZ⟩ : mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n w ∈
        Set.range fun Z : 𝔤 ↦ fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ 𝔤) (b i) :=
      hιT ▸ Set.mem_range_self w
    refine ⟨Submodule.Quotient.mk Z, b.ext fun i ↦ ?_⟩
    have hi := (congrFun hw i).trans (congrFun hZ i).symm
    rw [h.mfderiv_components_apply] at hi
    rw [Module.Dual.coadjointTangentMap_mk, hxn, hi]
  · rintro ⟨u, hu⟩
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨w, hw⟩ : (fun i ↦ (⁅Z, ι n⁆ : Module.Dual ℝ 𝔤) (b i)) ∈
        Set.range (mfderiv J 𝓘(ℝ, κ → ℝ) (fun m i ↦ ι m (b i)) n) :=
      hιT ▸ Set.mem_range_self Z
    refine ⟨w, funext fun i ↦ ?_⟩
    rw [h.mfderiv_components_apply, ← hu, Module.Dual.coadjointTangentMap_mk, hxn, hw]

end IsMomentMap

end SmoothTwoForm

end TauCeti
