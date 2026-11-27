/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.DiffeomorphProd
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Arnold
public import TauCeti.Topology.Sets.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# The saturated neighbourhood of a Liouville torus as a family of tori

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions with complete
Hamiltonian vector fields, generating the Hamiltonian flow action `v • y` of `ι → ℝ` on `M`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`). Let `s` be a smooth section of `F`
over an open set `D` of values, `F (s c) = c`, and let `P` be a smooth family of full lattices over
`D` whose lattice at `c` is the group of periods of `s c`, the stabilizer `Λ_c` of `s c` under the
flow action (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer`). Smooth bases of
these period lattices exist near a compact regular component of a level
(`exists_hamiltonianFlowStabilizer_section_eq_closure_of_isCompact`, in the namespace
`TauCeti.SmoothTwoForm.IsSymplectic`).

The family of tori of `P` is the orbit space `(D × ℝ^ι)/Λ` of the period translation action
`l +ᵥ (c, v) = (c, v + P c l)` (`TauCeti.periodAddAction`), a smooth manifold
(`TauCeti.isManifold_torusFamily`). This file shows that the sweep `(c, v) ↦ v • s c` of the
section by the flows descends to it,

`[c, v] ↦ v • s c` (`TauCeti.SmoothTwoForm.IsSymplectic.torusFamilyMap`),

and that the descended map is a diffeomorphism of `(D × ℝ^ι)/Λ` onto the open set `W` of points
reached from the section by the flows
(`TauCeti.SmoothTwoForm.IsSymplectic.torusFamilyDiffeomorph`). It lies over `D`: `F` reads off
the parameter `c`. So `W` is a union of whole orbits, the regular Liouville tori through the points
`s c`, and `W` is identified with the family of tori `ℝ^ι / Λ_c`, one for each value `c ∈ D`.
Composing with the global trivialization of the family of tori
(`TauCeti.torusFamilyDiffeomorphProd`) along a `ℤ`-basis of `Λ` indexed by `κ` gives a
diffeomorphism `D × ℝ^κ/ℤ^κ ≃ W` (`TauCeti.SmoothTwoForm.IsSymplectic.prodTorusDiffeomorph`), the
angle coordinates of `W`.

Injectivity holds because `F` separates the parameters and the periods of `s c` are exactly the
lattice of `c`; the local diffeomorphism property descends from that of the sweep
(`isLocalDiffeomorphOn_hamiltonianFlowAction_section`, in the same namespace). No isotropy of the
section is needed.

## Main definitions

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `torusFamilyMap`: the map `[c, v] ↦ v • s c` from the family of tori to `M`.
* `torusFamilyDiffeomorph`: the same map as a diffeomorphism onto its open image.
* `prodTorusDiffeomorph`: its composite with the global trivialization of the family of tori,
  a diffeomorphism `D × ℝ^κ/ℤ^κ ≃ W`, for a `ℤ`-basis of `Λ` indexed by `κ`.

## Main results

* `torusFamilyMap_mk`: the map on representatives.
* `apply_torusFamilyMap`: it lies over the parameter space.
* `injective_torusFamilyMap`: it is injective.
* `isLocalDiffeomorph_torusFamilyMap`: it is a smooth local diffeomorphism.
* `connectedComponentIn_subset_range_torusFamilyMap`: its image contains the regular connected
  component of the level through a point of the section.
* `coe_torusFamilyProjection_torusFamilyDiffeomorph_symm_apply`,
  `coe_fst_prodTorusDiffeomorph_symm_apply`: the inverse diffeomorphisms read off `F`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the period lattice and the torus bundle of a Lagrangian fibration).
-/

public section

noncomputable section

open Function Set Filter Module Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {U : TopologicalSpace.Opens (ι → ℝ)} (s : (ι → ℝ) → M) {Λ : Type*} [AddCommGroup Λ]
  (P : U → Λ →ₗ[ℤ] (ι → ℝ))
  (hper : ∀ (c : U) (l : Λ), P c l ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c))

/-! ### The descended sweep -/

/-- **The sweep of a section, descended to the family of tori.** Let `s` be a map from the open
set `U` of values to `M`, and `P` a family of lattices over `U` whose vectors at `c` are periods of
`s c`. The map `(c, v) ↦ v • s c` is invariant under the period translations `v ↦ v + P c l`, so it
descends to the family of tori `(U × ℝ^ι)/Λ`, the orbit space of `TauCeti.periodAddAction P`. -/
def torusFamilyMap :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (U × (ι → ℝ)) → M :=
  letI := periodAddAction P
  AddAction.orbitRelQuotientLift
    (fun p : U × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.2).toMul (s p.1))
    fun l p ↦ by
      rw [periodAddAction_vadd, hσ.hamiltonianFlowAction_add_apply]
      exact congrArg _ ((hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 (hper p.1 l))

/-- The descended sweep sends the class of `(c, v)` to `v • s c`. -/
@[simp]
theorem torusFamilyMap_mk (p : U × (ι → ℝ)) :
    letI := periodAddAction P
    hσ.torusFamilyMap hF hcomm hc s P hper (Quotient.mk _ p) =
      (hσ.hamiltonianFlowAction hF hcomm hc p.2).toMul (s p.1) :=
  letI := periodAddAction P
  AddAction.orbitRelQuotientLift_mk p

/-- The descended sweep composed with the orbit map is the sweep `(c, v) ↦ v • s c`. -/
theorem torusFamilyMap_comp_mk :
    letI := periodAddAction P
    hσ.torusFamilyMap hF hcomm hc s P hper ∘ Quotient.mk _ =
      fun p : U × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc p.2).toMul (s p.1) :=
  funext (hσ.torusFamilyMap_mk hF hcomm hc s P hper)

/-- **The descended sweep lies over the parameter space.** For a section `s` of `F` over `U`, the
point `[c, v]` is sent into the level `F⁻¹(c)`. -/
theorem apply_torusFamilyMap (hFs : ∀ c ∈ U, F (s c) = c)
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (U × (ι → ℝ))) :
    F (hσ.torusFamilyMap hF hcomm hc s P hper z) = torusFamilyProjection P z := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn with
  | h p => rw [torusFamilyMap_mk, hσ.apply_hamiltonianFlowAction hF hcomm hc,
      torusFamilyProjection_mk, hFs _ p.1.prop]

/-- The image of the descended sweep is the set of points reached from the section by the
flows. -/
theorem range_torusFamilyMap :
    range (hσ.torusFamilyMap hF hcomm hc s P hper) =
      {y | ∃ (c : U) (v : ι → ℝ), (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) = y} := by
  let _ := periodAddAction P
  ext y
  refine ⟨?_, fun ⟨c, v, h⟩ ↦
    ⟨Quotient.mk _ (c, v), (hσ.torusFamilyMap_mk hF hcomm hc s P hper (c, v)).trans h⟩⟩
  rintro ⟨z, rfl⟩
  induction z using Quotient.inductionOn with
  | h p => exact ⟨p.1, p.2, (hσ.torusFamilyMap_mk hF hcomm hc s P hper p).symm⟩

/-- **The swept set contains the regular components through the section.** If the connected
component of `s c` in its level consists of regular points of `F`, then it lies in the image of the
descended sweep: on a manifold of dimension `2 · |ι|` it is the orbit of `s c` under the flows. -/
theorem connectedComponentIn_subset_range_torusFamilyMap (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (c : U) (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F (s c)}) (s c),
      IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) :
    connectedComponentIn (F ⁻¹' {F (s c)}) (s c) ⊆
      range (hσ.torusFamilyMap hF hcomm hc s P hper) := by
  rw [← hσ.range_hamiltonianFlowAction_apply hF hcomm hc hdim hreg, range_torusFamilyMap]
  rintro _ ⟨v, rfl⟩
  exact ⟨c, v, rfl⟩

/-- **The descended sweep is injective.** If `s` is a section of `F` over `U` and every period of
`s c` lies in the lattice `P c`, then `[c, v] ↦ v • s c` is injective. -/
theorem injective_torusFamilyMap (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c)) :
    Injective (hσ.torusFamilyMap hF hcomm hc s P hper) := by
  let _ := periodAddAction P
  intro z z' hzz'
  induction z using Quotient.inductionOn with | h p => ?_
  induction z' using Quotient.inductionOn with | h p' => ?_
  obtain ⟨c, v⟩ := p
  obtain ⟨c', v'⟩ := p'
  -- The two points lie over the same value of `F`.
  have hcc' : c = c' := by
    have h := congrArg F hzz'
    rw [hσ.apply_torusFamilyMap hF hcomm hc s P hper hFs,
      hσ.apply_torusFamilyMap hF hcomm hc s P hper hFs, torusFamilyProjection_mk,
      torusFamilyProjection_mk] at h
    exact Subtype.ext h
  subst hcc'
  rw [hσ.torusFamilyMap_mk hF hcomm hc s P hper, hσ.torusFamilyMap_mk hF hcomm hc s P hper,
    hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc] at hzz'
  -- So `v - v'` is a vector of the lattice `P c`.
  refine Quotient.sound ((mem_orbit_periodAddAction_iff P).2 ⟨rfl, ?_⟩)
  simpa [neg_add_eq_sub] using neg_mem (hstab c _ hzz')

/-! ### The descended sweep is a local diffeomorphism -/

variable [∀ c, DiscreteTopology (LinearMap.range (P c))]
  [∀ c, IsZLattice ℝ (LinearMap.range (P c))]
  (hinj : ∀ c, Injective (P c))
  (hP : ∀ l, ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ fun c : U ↦ P c l)

include hinj hP in
/-- **The descended sweep is a local diffeomorphism.** On a manifold of dimension `2 · |ι|`, let
`s` be a smooth section of `F` over `U`, and `P` a smooth family of full lattices of periods of the
points of `s`. Then `[c, v] ↦ v • s c` is a smooth local diffeomorphism from the family of tori
`(U × ℝ^ι)/Λ` to `M`. -/
theorem isLocalDiffeomorph_torusFamilyMap (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
    IsLocalDiffeomorph (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I ∞
      (hσ.torusFamilyMap hF hcomm hc s P hper) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
  intro z
  induction z using Quotient.inductionOn with | h p => ?_
  -- Cancel the orbit map, a local diffeomorphism, on the right.
  refine IsLocalDiffeomorphAt.of_comp_right ?_ (isLocalDiffeomorph_torusFamily_mk P hinj hP p)
  rw [torusFamilyMap_comp_mk]
  -- On `U × ℝ^ι` the sweep is the sweep on `ℝ^ι × ℝ^ι` after the open inclusion and the swap.
  have hu : IsLocalDiffeomorphAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
      (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) ∞
      (fun p : U × (ι → ℝ) ↦ (p.2, (p.1 : ι → ℝ))) p :=
    (isLocalDiffeomorph_subtype_val p.1 |>.prodMap
      (by simpa using (Diffeomorph.refl 𝓘(ℝ, ι → ℝ) (ι → ℝ) ∞).isLocalDiffeomorph p.2)).comp
      (hg := (Diffeomorph.prodComm 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞).isLocalDiffeomorph _)
  exact hu.comp (hg := hσ.isLocalDiffeomorphOn_hamiltonianFlowAction_section hF hcomm hc hdim
    U.isOpen hs hFs ⟨(p.2, p.1), mem_univ _, p.1.prop⟩)

/-! ### The diffeomorphism onto the saturated neighbourhood -/

/-- **The family of tori is diffeomorphic to the set swept out by the section.** On a manifold of
dimension `2 · |ι|`, let `s` be a smooth section of `F` over `U`, and `P` a smooth family of full
lattices over `U` whose lattice at `c` is exactly the group of periods of `s c`. Then
`[c, v] ↦ v • s c` is a diffeomorphism from the family of tori `(U × ℝ^ι)/Λ` onto its image, the
open set of points reached from the section by the flows (`range_torusFamilyMap`). -/
def torusFamilyDiffeomorph (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
    AddAction.orbitRel.Quotient Λ (U × (ι → ℝ)) ≃ₘ⟮𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ), I⟯
      (hσ.isLocalDiffeomorph_torusFamilyMap hF hcomm hc s P hper hinj hP hdim hs hFs).image :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
  IsLocalDiffeomorph.diffeomorphOfInjective
    (hσ.isLocalDiffeomorph_torusFamilyMap hF hcomm hc s P hper hinj hP hdim hs hFs)
    (hσ.injective_torusFamilyMap hF hcomm hc s P hper hFs hstab)

/-- The diffeomorphism onto the swept set evaluates as the descended sweep. -/
@[simp]
theorem coe_torusFamilyDiffeomorph_apply (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c))
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (U × (ι → ℝ))) :
    (hσ.torusFamilyDiffeomorph hF hcomm hc s P hper hinj hP hdim hs hFs hstab z : M) =
      hσ.torusFamilyMap hF hcomm hc s P hper z :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ z

/-- The diffeomorphism onto the swept set lies over the values: the inverse sends `y` into the
torus over `F y`. -/
@[simp]
theorem coe_torusFamilyProjection_torusFamilyDiffeomorph_symm_apply
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c))
    (y : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
      (hσ.isLocalDiffeomorph_torusFamilyMap hF hcomm hc s P hper hinj hP hdim hs hFs).image) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
    torusFamilyProjection P
        ((hσ.torusFamilyDiffeomorph hF hcomm hc s P hper hinj hP hdim hs hFs hstab).symm y) =
      F y := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
  rw [← hσ.apply_torusFamilyMap hF hcomm hc s P hper hFs,
    ← hσ.coe_torusFamilyDiffeomorph_apply hF hcomm hc s P hper hinj hP hdim hs hFs hstab,
    Diffeomorph.apply_symm_apply]

/-- **Angle coordinates on the swept set.** For a `ℤ`-basis `b` of `Λ`, the family of tori is
trivialized by the period coordinates (`TauCeti.torusFamilyDiffeomorphProd`), so the swept set is
diffeomorphic to `U × ℝ^κ/ℤ^κ`, where `κ` indexes `b`: the class of `x ∈ ℝ^κ` over `c` goes to
`(∑ i, xᵢ P c (b i)) • s c` (`prodTorusDiffeomorph_apply`). -/
def prodTorusDiffeomorph {κ : Type*} [Fintype κ] (b : Basis κ ℤ Λ)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
    (U × AddAction.orbitRel.Quotient (Submodule.span ℤ (range (Pi.basisFun ℝ κ))) (κ → ℝ))
      ≃ₘ⟮𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, κ → ℝ), I⟯
      (hσ.isLocalDiffeomorph_torusFamilyMap hF hcomm hc s P hper hinj hP hdim hs hFs).image :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
  (torusFamilyDiffeomorphProd P b hinj hP).symm.trans
    (hσ.torusFamilyDiffeomorph hF hcomm hc s P hper hinj hP hdim hs hFs hstab)

/-- The angle coordinates send the class of `x` over `c` to `(∑ i, xᵢ P c (b i)) • s c`. -/
@[simp]
theorem prodTorusDiffeomorph_apply {κ : Type*} [Fintype κ] (b : Basis κ ℤ Λ)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c)) (c : U) (x : κ → ℝ) :
    (hσ.prodTorusDiffeomorph hF hcomm hc s P hper hinj hP b hdim hs hFs hstab
        (c, Quotient.mk _ x) : M) =
      (hσ.hamiltonianFlowAction hF hcomm hc (∑ i, x i • P c (b i))).toMul (s c) := by
  simp [prodTorusDiffeomorph, Basis.equivFun_symm_apply]

/-- The angle coordinates lie over the values: the parameter of the inverse image of `y` is
`F y`. -/
@[simp]
theorem coe_fst_prodTorusDiffeomorph_symm_apply {κ : Type*} [Fintype κ] (b : Basis κ ℤ Λ)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s U) (hFs : ∀ c ∈ U, F (s c) = c)
    (hstab : ∀ (c : U) (v : ι → ℝ), v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) →
      v ∈ LinearMap.range (P c))
    (y : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
      (hσ.isLocalDiffeomorph_torusFamilyMap hF hcomm hc s P hper hinj hP hdim hs hFs).image) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
    (((hσ.prodTorusDiffeomorph hF hcomm hc s P hper hinj hP b hdim hs hFs hstab).symm y).1 :
      ι → ℝ) = F y := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ι → ℝ) P (fun l ↦ (hP l).continuous) hinj
  simp [prodTorusDiffeomorph]

end IsSymplectic

end SmoothTwoForm

end TauCeti
