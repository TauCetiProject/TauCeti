/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.ContinuousDual.HahnModule
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The annihilator topology on the continuous residue dual

The continuous dual of `V((t))` carries a linear topology whose neighbourhoods of zero are the
annihilators of the lattices `U_(-a)(V)`. With this topology, the residue identification
`HahnModule.residueDualEquiv` is a continuous linear equivalence from `V*((t))` with its lattice
topology. Thus convergence of residue functionals means eventual agreement on each entire
lattice, not merely pointwise convergence on individual Laurent series.

The topology is available only in the scope `TauCeti.HahnModuleDualTopology`; it does not replace
any topology on spaces of continuous linear maps globally. No finite-dimensionality of `V` is
needed, and the coefficient ring may be any discrete commutative ring. Coefficientwise linear
maps induce continuous pullbacks on these duals, and the residue identification intertwines them
with coefficientwise transposes.

## Main definitions

* `TauCeti.HahnModuleDualTopology.annihilatorLattice`: functionals vanishing on `U_(-a)(V)`.
* `HahnModule.residueDualContinuousLinearEquiv`: the topological residue-dual identification.
* `LinearMap.hahnModuleDualMap`: pullback of continuous functionals along a coefficientwise map.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.

The algebraic identification and its annihilator computation are supplied by
`HahnModule.residueDualEquiv` and `HahnModule.lattice_le_ker_residueDual_iff`.
-/

public section

open Filter Topology

namespace TauCeti.HahnModuleDualTopology

open TauCeti.HahnModule

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [DiscreteTopology R]

/-- The annihilator of `U_(-a)(V)` in the continuous dual of `V((t))`. The sign makes these
submodules decrease with `a`, just like the lattices in `V*((t))`. -/
noncomputable def annihilatorLattice (a : ℤ) : Submodule R (HahnModule ℤ R V →L[R] R) :=
  (lattice R V (-a)).dualAnnihilator.comap (ContinuousLinearMap.coeLM R)

/-- Membership means vanishing on the whole lattice `U_(-a)(V)`. -/
theorem mem_annihilatorLattice_iff {a : ℤ} {ℓ : HahnModule ℤ R V →L[R] R} :
    ℓ ∈ annihilatorLattice R V a ↔ lattice R V (-a) ≤ LinearMap.ker ℓ.toLinearMap := by
  simp only [annihilatorLattice, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    ContinuousLinearMap.coeLM, LinearMap.coe_mk, AddHom.coe_mk, IsConcreteLE.le_iff,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- The annihilator neighbourhoods decrease with their index. -/
theorem annihilatorLattice_antitone : Antitone (annihilatorLattice R V) := by
  intro a b hab ℓ hℓ
  rw [mem_annihilatorLattice_iff] at hℓ ⊢
  exact fun f hf ↦ hℓ (lattice_antitone R V (neg_le_neg hab) hf)

/-- The annihilator lattices form a basis of submodules over the discrete coefficient ring. -/
theorem annihilatorSubmodulesBasis : SubmodulesBasis (annihilatorLattice R V) where
  inter a b := ⟨max a b, le_inf (annihilatorLattice_antitone R V (le_max_left a b))
    (annihilatorLattice_antitone R V (le_max_right a b))⟩
  smul ℓ a := by simp [nhds_discrete]

/-- The topology of uniform vanishing on lattices, scoped to avoid changing other topologies
on continuous linear maps. -/
noncomputable scoped instance instTopologicalSpace :
    TopologicalSpace (HahnModule ℤ R V →L[R] R) :=
  (annihilatorSubmodulesBasis R V).topology

scoped instance : IsTopologicalAddGroup (HahnModule ℤ R V →L[R] R) :=
  (annihilatorSubmodulesBasis R V).toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup

/-- The annihilators of `U_(-a)(V)` form a neighbourhood basis at zero. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : HahnModule ℤ R V →L[R] R)).HasBasis (fun _ : ℤ ↦ True)
      (fun a ↦ (annihilatorLattice R V a : Set (HahnModule ℤ R V →L[R] R))) := by
  let h := (annihilatorSubmodulesBasis R V).toModuleFilterBasis.toAddGroupFilterBasis
  refine h.nhds_zero_hasBasis.to_hasBasis ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨a, trivial, subset_rfl⟩
  · exact fun a _ ↦ ⟨_, ⟨a, rfl⟩, subset_rfl⟩

scoped instance : IsLinearTopology R (HahnModule ℤ R V →L[R] R) :=
  IsLinearTopology.mk_of_hasBasis R (hasBasis_nhds_zero R V)

scoped instance : ContinuousSMul R (HahnModule ℤ R V →L[R] R) :=
  (annihilatorSubmodulesBasis R V).toModuleFilterBasis.continuousSMul

/-- Convergence in the dual topology means eventual agreement with the limit on every lattice. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} (s : ι → HahnModule ℤ R V →L[R] R)
    (ℓ : HahnModule ℤ R V →L[R] R) :
    Tendsto s l (𝓝 ℓ) ↔
      ∀ a : ℤ, ∀ᶠ i in l, ∀ f ∈ lattice R V (-a), s i f = ℓ f := by
  rw [((hasBasis_nhds_zero R V).nhds_of_zero ℓ).tendsto_right_iff]
  simp [mem_annihilatorLattice_iff, IsConcreteLE.le_iff, LinearMap.mem_ker, sub_eq_zero]

/-- Every annihilator lattice is open in the dual topology. -/
theorem isOpen_annihilatorLattice (a : ℤ) :
    IsOpen (annihilatorLattice R V a : Set (HahnModule ℤ R V →L[R] R)) :=
  (annihilatorLattice R V a).toAddSubgroup.isOpen_of_mem_nhds
    ((hasBasis_nhds_zero R V).mem_of_mem trivial)

end TauCeti.HahnModuleDualTopology

open scoped TauCeti.HahnModuleDualTopology

namespace HahnModule

open TauCeti.HahnModule TauCeti.HahnModuleDualTopology

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [DiscreteTopology R]

/-- Residue pairing identifies the lattice `U_a(V*)` with the annihilator of `U_(-a)(V)`. -/
@[simp]
theorem residueDual_mem_annihilatorLattice_iff (g : HahnModule ℤ R (Module.Dual R V)) (a : ℤ) :
    residueDual g ∈ annihilatorLattice R V a ↔ g ∈ lattice R (Module.Dual R V) a := by
  simpa only [mem_annihilatorLattice_iff, neg_neg] using lattice_le_ker_residueDual_iff g (-a)

/-- The residue-dual identification is continuous for the annihilator topology. -/
theorem continuous_residueDualEquiv : Continuous (residueDualEquiv R V) := by
  -- Pin the lattice group structure before applying continuity at zero through the dual carrier.
  let : IsTopologicalAddGroup (HahnModule ℤ R (Module.Dual R V)) := inferInstance
  apply continuous_of_tendsto_nhds_zero (G := HahnModule ℤ R (Module.Dual R V))
    (M := HahnModule ℤ R V →L[R] R) (residueDualEquiv R V)
  exact ((hasBasis_nhds_zero_lattice R _).tendsto_iff (hasBasis_nhds_zero R V)).mpr
    fun a _ ↦ ⟨a, trivial, fun g hg ↦ by
      simpa only [residueDualEquiv_apply, SetLike.mem_coe] using
        (residueDual_mem_annihilatorLattice_iff R V g a).mpr hg⟩

/-- Reconstructing the dual-valued series from a continuous functional is continuous. -/
theorem continuous_residueDualEquiv_symm : Continuous (residueDualEquiv R V).symm := by
  -- Pin the lattice-topology instance: inference through the dual-module carrier is ambiguous.
  let : ContinuousAdd (HahnModule ℤ R (Module.Dual R V)) :=
    (inferInstance : IsTopologicalAddGroup (HahnModule ℤ R (Module.Dual R V))).toContinuousAdd
  apply continuous_of_tendsto_nhds_zero (residueDualEquiv R V).symm.toLinearMap
  refine ((hasBasis_nhds_zero R V).tendsto_iff (hasBasis_nhds_zero_lattice R _)).mpr
    fun a _ ↦ ⟨a, trivial, fun ℓ hℓ ↦ ?_⟩
  exact (residueDual_mem_annihilatorLattice_iff R V
    ((residueDualEquiv R V).symm ℓ) a).mp (by simpa using hℓ)

/-- Residue pairing is a homeomorphism and linear equivalence for the lattice topology on
`V*((t))` and the annihilator topology on the continuous dual of `V((t))`. -/
noncomputable def residueDualContinuousLinearEquiv :
    HahnModule ℤ R (Module.Dual R V) ≃L[R] (HahnModule ℤ R V →L[R] R) where
  toLinearEquiv := residueDualEquiv R V
  continuous_toFun := continuous_residueDualEquiv R V
  continuous_invFun := continuous_residueDualEquiv_symm R V

@[simp]
theorem residueDualContinuousLinearEquiv_apply (g : HahnModule ℤ R (Module.Dual R V)) :
    residueDualContinuousLinearEquiv R V g = residueDual g :=
  residueDualEquiv_apply g

@[simp]
theorem residueDualContinuousLinearEquiv_symm_apply (ℓ : HahnModule ℤ R V →L[R] R) :
    (residueDualContinuousLinearEquiv R V).symm ℓ = (residueDualEquiv R V).symm ℓ :=
  (rfl)

end HahnModule

namespace TauCeti.HahnModuleDualTopology

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [DiscreteTopology R]

/-- The annihilator topology on the continuous residue dual is Hausdorff. -/
scoped instance : T2Space (HahnModule ℤ R V →L[R] R) :=
  (HahnModule.residueDualContinuousLinearEquiv R V).symm.toHomeomorph.isEmbedding.t2Space

end TauCeti.HahnModuleDualTopology

namespace LinearMap

open TauCeti.HahnModule TauCeti.HahnModuleDualTopology HahnModule

variable {R V W U : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]
  [TopologicalSpace R] [DiscreteTopology R]

/-- Pullback of continuous residue functionals along a coefficientwise linear map. It is
continuous for the annihilator topologies, since coefficientwise maps preserve lattices. -/
noncomputable def hahnModuleDualMap (u : V →ₗ[R] W) :
    (HahnModule ℤ R W →L[R] R) →L[R] (HahnModule ℤ R V →L[R] R) := by
  let f : (HahnModule ℤ R W →L[R] R) →ₗ[R] (HahnModule ℤ R V →L[R] R) :=
    u.hahnModuleMap.lcomp R
  refine ⟨f, continuous_of_continuousAt_zero f ?_⟩
  rw [ContinuousAt, map_zero]
  refine ((hasBasis_nhds_zero R W).tendsto_iff (hasBasis_nhds_zero R V)).mpr
    fun a _ ↦ ⟨a, trivial, fun ℓ hℓ ↦ ?_⟩
  rw [SetLike.mem_coe, mem_annihilatorLattice_iff] at hℓ ⊢
  intro x hx
  apply hℓ
  exact u.hahnModuleMap_mem_lattice hx

@[simp]
theorem hahnModuleDualMap_apply (u : V →ₗ[R] W) (ℓ : HahnModule ℤ R W →L[R] R)
    (f : HahnModule ℤ R V) : u.hahnModuleDualMap ℓ f = ℓ (u.hahnModuleMap f) :=
  (rfl)

@[simp]
theorem hahnModuleDualMap_id :
    (LinearMap.id : V →ₗ[R] V).hahnModuleDualMap = .id R _ := by
  apply ContinuousLinearMap.ext
  intro ℓ
  ext f
  simp

@[simp]
theorem hahnModuleDualMap_comp (v : W →ₗ[R] U) (u : V →ₗ[R] W) :
    (v.comp u).hahnModuleDualMap = u.hahnModuleDualMap.comp v.hahnModuleDualMap := by
  apply ContinuousLinearMap.ext
  intro ℓ
  ext f
  simp only [hahnModuleDualMap_apply, ContinuousLinearMap.comp_apply, hahnModuleMap_comp]

/-- The topological residue-dual identification is natural: pullback corresponds to applying
the transpose to every coefficient. -/
@[simp]
theorem hahnModuleDualMap_residueDual (u : V →ₗ[R] W) (g : HahnModule ℤ R (Module.Dual R W)) :
    u.hahnModuleDualMap (residueDual g) = residueDual (u.dualMap.hahnModuleMap g) := by
  apply ContinuousLinearMap.ext
  intro f
  simpa only [hahnModuleDualMap_apply] using u.residueDual_hahnModuleMap g f

end LinearMap
