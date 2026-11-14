/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.Quotient.Descent
public import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
public import TauCeti.Geometry.Symplectic.Lagrangian.Fibration
public import TauCeti.Geometry.Symplectic.Manifold.Quotient
public import TauCeti.Topology.FiberBundle.Countable
public import TauCeti.Topology.FiberBundle.Separation
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.ZMultiples

/-!
# The quotient of a cotangent bundle by the lattice of a coframe

Let `α : ι → SmoothForm I B ℝ 1` be one-forms on a manifold `B` whose values form a basis of
every cotangent space, that is, whose sections form a global frame of `T*B` in the sense of
Mathlib's `IsLocalFrameOn` on `univ`. At each point `x` the integer combinations
`∑ i, k i • α i x` form a full lattice `Λ_x` in `T*_x B`, and the integer vectors `k : ι → ℤ`
act on `T*B` by translating each fibre by `∑ i, k i • α i`
(`TauCeti.CotangentBundle.latticeForm α k`). This file constructs the quotient

`T*B/Λ = TauCeti.CotangentBundle.LatticeQuotient α hα`

and shows that its projection to `B` is a proper submersion with compact connected fibres, which
are Lagrangian when the `α i` are closed.

* The translation action of `Multiplicative (ι → ℤ)` on `T*B` (on the type synonym
  `TauCeti.CotangentBundle.LatticeCover α hα`) is smooth and free, and it is properly
  discontinuous because the coordinates of a covector in the frame depend continuously on the
  covector and are shifted by `k`. So when `B` is a Hausdorff manifold modelled on a
  finite-dimensional space, `T*B/Λ` is a smooth manifold and the orbit map
  `TauCeti.CotangentBundle.LatticeQuotient.mk` is a local diffeomorphism.
* The bundle projection descends to a proper submersion
  `TauCeti.CotangentBundle.LatticeQuotient.proj hα : T*B/Λ → B`. Its fibre over `x` is the image
  of the unit cube under `c ↦ [x, ∑ i, c i • α i x]`, so it is compact and connected.
* If the forms `α i` are closed, every translation preserves the canonical symplectic form
  `ω = -dλ`
  (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff`),
  so `ω` descends to a symplectic form on `T*B/Λ`
  (`TauCeti.CotangentBundle.LatticeQuotient.symplecticForm`). Since the fibres of `T*B → B` are
  Lagrangian (`TauCeti.CotangentBundle.isLagrangian_ker_mfderiv_proj`), so are the fibres of
  `T*B/Λ → B`. The section `x ↦ [β x]` of `T*B/Λ` defined by a one-form `β` is Lagrangian
  exactly when `β` is closed; in particular the zero section descends to a Lagrangian section.

This is the canonical model of action-angle theory for a period lattice spanned by global closed
one-forms, such as the differentials of global action coordinates.

## Main definitions

* `TauCeti.CotangentBundle.latticeForm α k`: the integer combination `∑ i, k i • α i`.
* `TauCeti.CotangentBundle.LatticeCover α hα`: the cotangent bundle, with the translation action
  of `Multiplicative (ι → ℤ)`.
* `TauCeti.CotangentBundle.LatticeQuotient α hα`: its orbit space `T*B/Λ`.
* `TauCeti.CotangentBundle.LatticeQuotient.mk`, `TauCeti.CotangentBundle.LatticeQuotient.proj`:
  the quotient map `T*B → T*B/Λ` and the projection `T*B/Λ → B`.
* `TauCeti.CotangentBundle.LatticeQuotient.symplecticForm`: the descended symplectic form.

## Main results

* `TauCeti.CotangentBundle.LatticeQuotient.mk_eq_mk_iff`: two covectors have the same class
  exactly when they differ by a lattice vector.
* `TauCeti.CotangentBundle.LatticeQuotient.isLocalDiffeomorph_mk`: the quotient map is a local
  diffeomorphism.
* `TauCeti.CotangentBundle.LatticeQuotient.isSubmersionOfComplement_proj`,
  `TauCeti.CotangentBundle.LatticeQuotient.isProperMap_proj`: the projection is a proper
  submersion.
* `TauCeti.CotangentBundle.LatticeQuotient.isCompact_proj_preimage_singleton`,
  `TauCeti.CotangentBundle.LatticeQuotient.isConnected_proj_preimage_singleton`: its fibres are
  compact and connected.
* `TauCeti.CotangentBundle.LatticeQuotient.mpullback_mk_symplecticForm`,
  `TauCeti.CotangentBundle.LatticeQuotient.isSymplectic_symplecticForm`: the descended form pulls
  back to `ω` and is symplectic.
* `TauCeti.CotangentBundle.LatticeQuotient.isLagrangian_ker_mfderiv_proj`: the fibres of the
  projection are Lagrangian.
* `TauCeti.CotangentBundle.LatticeQuotient.isLagrangianTorusFibration_proj`: the projection is a
  regular Lagrangian torus fibration.
* `TauCeti.CotangentBundle.LatticeQuotient.isLagrangianMap_mk_comp_section_iff`: the section
  defined by a one-form is Lagrangian exactly when the form is closed.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (the period lattice `Λ ⊂ T*B` and the torus bundle `T*B/Λ`).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [IsManifold I ∞ B] {ι : Type*} [Fintype ι]

/-! ### Integer combinations of one-forms -/

/-- The integer combination `∑ i, k i • α i` of a finite family of one-forms. Translating the
fibres of `T*B` by these forms is the action of the lattice spanned by the `α i`. -/
def latticeForm (α : ι → SmoothForm I B ℝ 1) (k : ι → ℤ) : SmoothForm I B ℝ 1 :=
  ∑ i, (k i : ℝ) • α i

/-- The covector of `latticeForm α k` at `x` is the integer combination of the covectors of the
`α i` at `x`. -/
@[simp]
theorem degreeOneEquiv_latticeForm_apply (α : ι → SmoothForm I B ℝ 1) (k : ι → ℤ) (x : B) :
    SmoothForm.degreeOneEquiv (latticeForm α k) x =
      ∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) x := by
  simp only [latticeForm, map_sum, map_smul]
  rw [← ContMDiffSection.coeAddHom_apply, map_sum, Finset.sum_apply]
  simp

/-- Integer combinations of closed one-forms are closed. -/
theorem isClosed_latticeForm {α : ι → SmoothForm I B ℝ 1} (hclosed : ∀ i, (α i).IsClosed)
    (k : ι → ℤ) : (latticeForm α k).IsClosed := by
  rw [latticeForm, SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_smul, (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).1 (hclosed i), smul_zero]

/-! ### The translation action of the lattice -/

variable {α : ι → SmoothForm I B ℝ 1}

variable (α) in
/-- The cotangent bundle of `B`, carrying the action of `Multiplicative (ι → ℤ)` by which `k`
translates each fibre by `∑ i, k i • α i`. Here the `α i` form a global frame of `T*B`. It is a
type synonym of `TauCeti.CotangentBundle I B`, with the same topology and manifold structure, so
that the cotangent bundle itself does not acquire an `α`-dependent action. -/
@[expose] def LatticeCover
    (_hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ) :
    Type _ :=
  CotangentBundle I B

namespace LatticeCover

variable (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ)

instance : TopologicalSpace (LatticeCover α hα) :=
  inferInstanceAs (TopologicalSpace (CotangentBundle I B))

instance [T2Space B] : T2Space (LatticeCover α hα) :=
  inferInstanceAs (T2Space (CotangentBundle I B))

instance : ChartedSpace (ModelProd H (E →L[ℝ] ℝ)) (LatticeCover α hα) :=
  inferInstanceAs (ChartedSpace (ModelProd H (E →L[ℝ] ℝ)) (CotangentBundle I B))

instance : IsManifold (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (LatticeCover α hα) :=
  inferInstanceAs (IsManifold (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (CotangentBundle I B))

instance [FiniteDimensional ℝ E] : LocallyCompactSpace (LatticeCover α hα) :=
  Manifold.locallyCompact_of_finiteDimensional (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))

instance [FiniteDimensional ℝ E] [SecondCountableTopology B] :
    SecondCountableTopology (LatticeCover α hα) :=
  inferInstanceAs (SecondCountableTopology (CotangentBundle I B))

/-- The identification of the cotangent bundle with the cover. -/
def ofCotangent : CotangentBundle I B ≃ LatticeCover α hα := Equiv.refl _

/- `LatticeCover α hα` carries the manifold structure of the cotangent bundle, and `ofCotangent hα`
is the identity of the underlying type, so its regularity is that of the identity map. -/

omit [Fintype ι] in
/-- The identification of the cotangent bundle with the cover is smooth. -/
theorem contMDiff_ofCotangent :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (ofCotangent hα) :=
  contMDiff_id

omit [Fintype ι] in
/-- The identification of the cover with the cotangent bundle is smooth. -/
theorem contMDiff_ofCotangent_symm :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (ofCotangent hα).symm :=
  contMDiff_id

instance : SMul (Multiplicative (ι → ℤ)) (LatticeCover α hα) where
  smul k z := ofCotangent hα (vectorBundleTranslateDiffeomorph
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd))
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff ((ofCotangent hα).symm z))

/-- The integer vector `k` acts on the cover by the fibre translation by `latticeForm α k`. -/
theorem smul_def (k : Multiplicative (ι → ℤ)) (z : LatticeCover α hα) :
    k • z = ofCotangent hα (vectorBundleTranslateDiffeomorph
      (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd))
      (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff ((ofCotangent hα).symm z)) :=
  (rfl)

/-- The integer vector `k` sends a covector `p` over `x` to `p + ∑ i, k i • α i x`. -/
@[simp]
theorem smul_ofCotangent (k : Multiplicative (ι → ℤ)) (z : CotangentBundle I B) :
    k • ofCotangent hα z = ofCotangent hα
      ⟨z.proj, z.2 + ∑ i, (k.toAdd i : ℝ) • SmoothForm.degreeOneEquiv (α i) z.proj⟩ := by
  rw [smul_def, Equiv.symm_apply_apply, vectorBundleTranslateDiffeomorph_apply,
    degreeOneEquiv_latticeForm_apply]

/-- `Multiplicative (ι → ℤ)` acts on the cover by translating each fibre by the integer
combinations of the `α i`. -/
instance : MulAction (Multiplicative (ι → ℤ)) (LatticeCover α hα) where
  one_smul z := by
    obtain ⟨z, rfl⟩ := (ofCotangent hα).surjective z
    simp
  mul_smul j k z := by
    obtain ⟨z, rfl⟩ := (ofCotangent hα).surjective z
    simp only [smul_ofCotangent, toAdd_mul, Pi.add_apply, Int.cast_add, add_smul,
      Finset.sum_add_distrib]
    congr 2
    abel

/-- The coordinates `c` of a covector `p = ∑ i, c i • α i x` in the frame. -/
private def coord (z : CotangentBundle I B) : ι → ℝ := fun i ↦ hα.coeff i z.proj z.2

omit [Fintype ι] in
private theorem continuous_coord [FiniteDimensional ℝ E] : Continuous (coord hα) :=
  continuous_pi fun i ↦ continuousOn_univ.mp (hα.continuousOn_coeff_totalSpace isOpen_univ i)

/-- Translating by the lattice vector of `k` shifts the coordinates by `k`. -/
private theorem coord_add_sum (x : B) (p : TangentSpace I x →L[ℝ] ℝ) (k : ι → ℤ) :
    coord hα ⟨x, p + ∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) x⟩ =
      coord hα ⟨x, p⟩ + fun i ↦ (k i : ℝ) := by
  classical
  funext i
  have h (j : ι) :
      hα.coeff i x (SmoothForm.degreeOneEquiv (α j) x) = if j = i then 1 else 0 := by
    rw [hα.coeff_apply_of_mem (mem_univ x) (fun x ↦ SmoothForm.degreeOneEquiv (α j) x),
      ← hα.toBasisAt_coe (mem_univ x), Module.Basis.repr_self, Finsupp.single_apply]
  simp [coord, map_sum, h]

/-- The action is properly discontinuous: only finitely many integer vectors translate a compact
set to meet another compact set. -/
instance [FiniteDimensional ℝ E] :
    ProperlyDiscontinuousSMul (Multiplicative (ι → ℤ)) (LatticeCover α hα) where
  finite_disjoint_inter_image {K L} hK hL := by
    set c : LatticeCover α hα → ι → ℝ := fun w ↦ coord hα ((ofCotangent hα).symm w)
    have hc : Continuous c := continuous_coord hα
    -- If `k • z ∈ L` for some `z ∈ K`, then `k` is the difference of the coordinates of a point
    -- of `L` and a point of `K`, which lies in a compact set.
    set C := (fun w : LatticeCover α hα × LatticeCover α hα ↦ c w.1 - c w.2) '' L ×ˢ K
    have hC : IsCompact C :=
      (hL.prod hK).image ((hc.comp continuous_fst).sub (hc.comp continuous_snd))
    have hfin : {k : ι → ℤ | (fun i ↦ (k i : ℝ)) ∈ C}.Finite := by
      refine (Set.Finite.pi (t := fun i ↦ {n : ℤ | (n : ℝ) ∈ (fun v : ι → ℝ ↦ v i) '' C})
        fun i ↦ ?_).subset fun k hk i _ ↦ ⟨_, hk, rfl⟩
      exact tendsto_cofinite_cocompact_iff.mp Int.tendsto_coe_cofinite _
        (hC.image (continuous_apply i))
    refine (hfin.preimage Multiplicative.toAdd.injective.injOn).subset fun k hk ↦ ?_
    obtain ⟨_, ⟨z, hz, rfl⟩, hkz⟩ := hk
    refine ⟨(k • z, z), ⟨hkz, hz⟩, ?_⟩
    obtain ⟨z, rfl⟩ := (ofCotangent hα).surjective z
    simp only [c, smul_ofCotangent, Equiv.symm_apply_apply]
    rw [coord_add_sum]
    simp

/-- The action is by homeomorphisms. -/
instance : ContinuousConstSMul (Multiplicative (ι → ℤ)) (LatticeCover α hα) where
  continuous_const_smul k := by
    simp_rw [smul_def]
    exact (vectorBundleTranslateDiffeomorph (IB := I) (F := E →L[ℝ] ℝ)
      (V := fun x : B ↦ TangentSpace I x →L[ℝ] ℝ) _
      (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff).continuous

/-- The action is by smooth maps. -/
instance : ContMDiffConstSMul (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (Multiplicative (ι → ℤ))
    (LatticeCover α hα) where
  contMDiff_const_smul k := by
    simp_rw [smul_def]
    exact (vectorBundleTranslateDiffeomorph (IB := I) (F := E →L[ℝ] ℝ)
      (V := fun x : B ↦ TangentSpace I x →L[ℝ] ℝ) _
      (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff).contMDiff

/-- The action is free, since the `α i` are linearly independent at every point. -/
instance : IsCancelSMul (Multiplicative (ι → ℤ)) (LatticeCover α hα) where
  left_cancel' k _ _ h := smul_left_cancel k h
  right_cancel' j k z h := by
    obtain ⟨z, rfl⟩ := (ofCotangent hα).surjective z
    simp only [smul_ofCotangent] at h
    have h' := TotalSpace.mk_inj.mp ((ofCotangent hα).injective h)
    simp only [add_right_inj] at h'
    have hlin := Fintype.linearIndependent_iff.mp (hα.linearIndependent (mem_univ z.proj))
      (fun i ↦ ((j.toAdd i : ℝ) - k.toAdd i)) (by simp [sub_smul, Finset.sum_sub_distrib, h'])
    apply Multiplicative.toAdd.injective
    funext i
    exact_mod_cast sub_eq_zero.mp (hlin i)

end LatticeCover

variable (α) in
/-- **The quotient `T*B/Λ`** of the cotangent bundle by the lattice `Λ` spanned at every point by
a global frame `α i` of one-forms: the orbit space of the translation action of
`Multiplicative (ι → ℤ)` on `T*B`. It is a smooth manifold when `B` is a Hausdorff manifold
modelled on a finite-dimensional space. -/
abbrev LatticeQuotient
    (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ) :
    Type _ :=
  MulAction.orbitRel.Quotient (Multiplicative (ι → ℤ)) (LatticeCover α hα)

namespace LatticeQuotient

open LatticeCover

variable (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ)

/-! ### The quotient map and the projection -/

/-- The class in `T*B/Λ` of a covector. -/
def mk (z : CotangentBundle I B) : LatticeQuotient α hα := Quotient.mk _ (ofCotangent hα z)

/-- The class of a covector is its orbit, read in the cover. -/
theorem mk_def (z : CotangentBundle I B) : mk hα z = Quotient.mk _ (ofCotangent hα z) := (rfl)

/-- Every point of `T*B/Λ` is the class of a covector. -/
theorem mk_surjective : Function.Surjective (mk hα) := fun z ↦ by
  obtain ⟨w, rfl⟩ := Quotient.mk_surjective z
  exact ⟨(ofCotangent hα).symm w, rfl⟩

/-- Two covectors have the same class in `T*B/Λ` exactly when they differ by a lattice vector. -/
theorem mk_eq_mk_iff {z w : CotangentBundle I B} :
    mk hα z = mk hα w ↔ ∃ k : ι → ℤ,
      z = ⟨w.proj, w.2 + ∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) w.proj⟩ := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [smul_ofCotangent] at hk
    exact ⟨k.toAdd, ((ofCotangent hα).injective hk).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Multiplicative.ofAdd k, by rw [smul_ofCotangent]; rfl⟩

/-- Two covectors over the same point have the same class in `T*B/Λ` exactly when they differ by
an integer combination of the `α i` at that point. -/
theorem mk_mk_eq_mk_mk_iff {x : B} {p q : TangentSpace I x →L[ℝ] ℝ} :
    mk hα ⟨x, p⟩ = mk hα ⟨x, q⟩ ↔
      ∃ k : ι → ℤ, p = q + ∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) x := by
  rw [mk_eq_mk_iff]
  exact exists_congr fun _ ↦ TotalSpace.mk_inj

/-- The quotient map `T*B → T*B/Λ` is continuous. -/
theorem continuous_mk : Continuous (mk hα) := continuous_quot_mk

private theorem proj_smul (k : Multiplicative (ι → ℤ)) (z : LatticeCover α hα) :
    ((ofCotangent hα).symm (k • z)).proj = ((ofCotangent hα).symm z).proj := by
  obtain ⟨z, rfl⟩ := (ofCotangent hα).surjective z
  simp only [smul_ofCotangent, Equiv.symm_apply_apply]

/-- The projection `T*B/Λ → B`, descended from the bundle projection `T*B → B`. -/
def proj : LatticeQuotient α hα → B :=
  MulAction.orbitRelQuotientLift (G := Multiplicative (ι → ℤ))
    (fun z ↦ ((ofCotangent hα).symm z).proj) (proj_smul hα)

/-- The class of a covector over `x` lies over `x`. -/
@[simp]
theorem proj_mk (z : CotangentBundle I B) : proj hα (mk hα z) = z.proj :=
  MulAction.orbitRelQuotientLift_mk (ofCotangent hα z)

/-- The projection `T*B/Λ → B` lifts the bundle projection `T*B → B`. -/
theorem proj_comp_mk : proj hα ∘ mk hα = TotalSpace.proj :=
  funext (proj_mk hα)

/-! ### The fibres of the projection -/

/-- The map `(x, c) ↦ ∑ i, c i • α i x` is smooth. -/
private theorem contMDiff_sum_smul :
    ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun q : B × (ι → ℝ) ↦ (⟨q.1, ∑ i, q.2 i • SmoothForm.degreeOneEquiv (α i) q.1⟩ :
        CotangentBundle I B)) :=
  ContMDiff.sum_sectionAlong _ _ contMDiff_fst fun i _ ↦
    ContMDiff.smul_totalSpace (a := fun q : B × (ι → ℝ) ↦ q.2 i)
      (g := fun q : B × (ι → ℝ) ↦ (⟨q.1, SmoothForm.degreeOneEquiv (α i) q.1⟩ :
        CotangentBundle I B))
      ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).contMDiff.comp contMDiff_snd)
      ((SmoothForm.degreeOneEquiv (α i)).contMDiff.comp contMDiff_fst)

private theorem continuous_mk_sum_smul :
    Continuous fun q : B × (ι → ℝ) ↦
      mk hα ⟨q.1, ∑ i, q.2 i • SmoothForm.degreeOneEquiv (α i) q.1⟩ :=
  (continuous_mk hα).comp (contMDiff_sum_smul (α := α)).continuous

/-- Every class is represented by a covector whose coordinates in the frame lie in the unit
cube: the fractional parts of the coordinates of any representative. -/
theorem exists_mem_Icc_mk_eq (z : CotangentBundle I B) :
    ∃ c ∈ Set.pi univ fun _ : ι ↦ Icc (0 : ℝ) 1,
      mk hα ⟨z.proj, ∑ i, c i • SmoothForm.degreeOneEquiv (α i) z.proj⟩ = mk hα z := by
  obtain ⟨x, v⟩ := z
  set b := hα.toBasisAt (mem_univ x)
  set a : ι → ℝ := fun i ↦ b.repr v i
  refine ⟨fun i ↦ Int.fract (a i), fun i _ ↦ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
  rw [mk_mk_eq_mk_mk_iff]
  refine ⟨fun i ↦ -⌊a i⌋, ?_⟩
  have hz : v = ∑ i, a i • SmoothForm.degreeOneEquiv (α i) x := by
    simpa [b, a] using (b.sum_repr v).symm
  rw [hz, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← add_smul, Int.cast_neg, ← sub_eq_add_neg, Int.self_sub_floor]

/-- The fibre of `T*B/Λ` over `x` is the image of the unit cube under
`c ↦ [x, ∑ i, c i • α i x]`. -/
theorem proj_preimage_singleton (x : B) :
    proj hα ⁻¹' {x} =
      (fun c : ι → ℝ ↦ mk hα ⟨x, ∑ i, c i • SmoothForm.degreeOneEquiv (α i) x⟩) ''
        Set.pi univ fun _ ↦ Icc 0 1 := by
  ext y
  obtain ⟨z, rfl⟩ := mk_surjective hα y
  simp only [mem_preimage, proj_mk, mem_singleton_iff, mem_image]
  constructor
  · rintro rfl
    exact exists_mem_Icc_mk_eq hα z
  · rintro ⟨c, -, hc⟩
    simpa using (congrArg (proj hα) hc).symm

/-- The fibres of `T*B/Λ → B` are compact. -/
theorem isCompact_proj_preimage_singleton (x : B) : IsCompact (proj hα ⁻¹' {x}) := by
  rw [proj_preimage_singleton]
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).image
    ((continuous_mk_sum_smul hα).comp (Continuous.prodMk_right x))

/-- The fibres of `T*B/Λ → B` are connected. -/
theorem isConnected_proj_preimage_singleton (x : B) : IsConnected (proj hα ⁻¹' {x}) := by
  rw [proj_preimage_singleton]
  exact (isConnected_univ_pi.mpr fun _ ↦ isConnected_Icc zero_le_one).image _
    ((continuous_mk_sum_smul hα).comp (Continuous.prodMk_right x)).continuousOn

/-! ### The manifold structure -/

section Manifold

variable [FiniteDimensional ℝ E] [T2Space B]

/-- The quotient map `T*B → T*B/Λ` is a local diffeomorphism. -/
theorem isLocalDiffeomorph_mk :
    IsLocalDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (mk hα) :=
  isLocalDiffeomorph_quotientMk (G := Multiplicative (ι → ℤ)) (M := LatticeCover α hα)
    (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (n := ∞)

/-- The quotient map `T*B → T*B/Λ` is smooth. -/
theorem contMDiff_mk :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (mk hα) :=
  (isLocalDiffeomorph_mk hα).contMDiff

/-- The projection `T*B/Λ → B` is smooth. -/
theorem contMDiff_proj : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ (proj hα) :=
  (contMDiff_orbitRelQuotientLift_iff (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) le_rfl).mpr
    (Bundle.contMDiff_proj (IB := I) (F := E →L[ℝ] ℝ) (fun x : B ↦ TangentSpace I x →L[ℝ] ℝ))

/-- The projection `T*B/Λ → B` is a submersion, with the cotangent fibre as complement. -/
theorem isSubmersionOfComplement_proj :
    Manifold.IsSubmersionOfComplement (E →L[ℝ] ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ (proj hα) := by
  refine Manifold.isSubmersionOfComplement_iff.mpr fun y ↦ ?_
  obtain ⟨z, rfl⟩ := mk_surjective hα y
  refine (isLocalDiffeomorph_mk hα z).isSubmersionAtOfComplement_comp_iff.mp ?_
  rw [proj_comp_mk]
  exact Manifold.isSubmersionOfComplement_iff.mp
    (Bundle.isSubmersionOfComplement_proj (IB := I) (F := E →L[ℝ] ℝ)
      (V := fun x : B ↦ TangentSpace I x →L[ℝ] ℝ)) z

/-- The projection `T*B/Λ → B` is proper: the preimage of a compact set `K` is the image of
`K` times the unit cube. -/
theorem isProperMap_proj : IsProperMap (proj hα) := by
  have : LocallyCompactSpace B := Manifold.locallyCompact_of_finiteDimensional I
  refine isProperMap_iff_isCompact_preimage.mpr ⟨(contMDiff_proj hα).continuous, fun K hK ↦ ?_⟩
  have h : proj hα ⁻¹' K = (fun q : B × (ι → ℝ) ↦
      mk hα ⟨q.1, ∑ i, q.2 i • SmoothForm.degreeOneEquiv (α i) q.1⟩) ''
        K ×ˢ Set.pi univ fun _ ↦ Icc 0 1 := by
    ext y
    obtain ⟨z, rfl⟩ := mk_surjective hα y
    simp only [mem_preimage, proj_mk, mem_image, mem_prod, Prod.exists]
    constructor
    · intro hz
      obtain ⟨c, hc, hmk⟩ := exists_mem_Icc_mk_eq hα z
      exact ⟨z.proj, c, ⟨hz, hc⟩, hmk⟩
    · rintro ⟨x, c, ⟨hx, -⟩, hmk⟩
      have h := congrArg (proj hα) hmk
      rw [proj_mk, proj_mk] at h
      exact h ▸ hx
  rw [h]
  exact (hK.prod (isCompact_univ_pi fun _ ↦ isCompact_Icc)).image (continuous_mk_sum_smul hα)

/-! ### The symplectic form -/

/-- The canonical symplectic form of `T*B`, read on the cover. -/
private def coverForm : SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (LatticeCover α hα) :=
  SmoothForm.mpullback (ofCotangent hα).symm (contMDiff_ofCotangent_symm hα)
    (CotangentBundle.symplecticForm I B)

omit [FiniteDimensional ℝ E] [T2Space B] in
private theorem mpullback_smul_coverForm (hclosed : ∀ i, (α i).IsClosed)
    (k : Multiplicative (ι → ℤ)) :
    SmoothForm.mpullback (k • ·) (contMDiff_const_smul k) (coverForm hα) = coverForm hα := by
  set T := vectorBundleTranslateDiffeomorph (IB := I) (F := E →L[ℝ] ℝ)
    (V := fun x : B ↦ TangentSpace I x →L[ℝ] ℝ) _
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff
  -- On the cover, the action of `k` is the fibre translation `T` by `latticeForm α k`, which is
  -- symplectic because `latticeForm α k` is closed.
  calc SmoothForm.mpullback (k • ·) (contMDiff_const_smul k) (coverForm hα)
      = SmoothForm.mpullback (T ∘ (ofCotangent hα).symm)
          (T.contMDiff.comp (contMDiff_ofCotangent_symm hα))
          (CotangentBundle.symplecticForm I B) :=
        SmoothForm.mpullback_mpullback _ (ofCotangent hα).symm _ (contMDiff_ofCotangent_symm hα) _
    _ = coverForm hα := by
      rw [← SmoothForm.mpullback_mpullback (ofCotangent hα).symm T (contMDiff_ofCotangent_symm hα)
        T.contMDiff, coverForm,
        (CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff
          _).mpr (isClosed_latticeForm hclosed k.toAdd)]

/-- **The symplectic form of `T*B/Λ`.** When the frame consists of closed one-forms, the
canonical symplectic form `ω = -dλ` of `T*B` is invariant under the lattice translations and
descends to `T*B/Λ`. -/
def symplecticForm (hclosed : ∀ i, (α i).IsClosed) :
    SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (LatticeQuotient α hα) :=
  SmoothForm.descend (coverForm hα) (mpullback_smul_coverForm hα hclosed)

/-- The symplectic form of `T*B/Λ` pulls back along the quotient map to the canonical symplectic
form of `T*B`. -/
theorem mpullback_mk_symplecticForm (hclosed : ∀ i, (α i).IsClosed) :
    SmoothForm.mpullback (mk hα) (contMDiff_mk hα) (symplecticForm hα hclosed) =
      CotangentBundle.symplecticForm I B := by
  calc SmoothForm.mpullback (mk hα) (contMDiff_mk hα) (symplecticForm hα hclosed)
      = SmoothForm.mpullback (ofCotangent hα) (contMDiff_ofCotangent hα)
          (SmoothForm.mpullback (Quotient.mk _) isLocalDiffeomorph_quotientMk.contMDiff
            (symplecticForm hα hclosed)) := (SmoothForm.mpullback_mpullback _ _ _ _ _).symm
    _ = SmoothForm.mpullback ((ofCotangent hα).symm ∘ ofCotangent hα)
          ((contMDiff_ofCotangent_symm hα).comp (contMDiff_ofCotangent hα))
          (CotangentBundle.symplecticForm I B) := by
      rw [symplecticForm, SmoothForm.mpullback_quotientMk_descend, coverForm,
        SmoothForm.mpullback_mpullback]
    _ = CotangentBundle.symplecticForm I B :=
      -- `ofCotangent hα` is the identity of the underlying type.
      LinearMap.congr_fun SmoothForm.mpullback_id _

/-- The descended form on `T*B/Λ` is symplectic. -/
theorem isSymplectic_symplecticForm (hclosed : ∀ i, (α i).IsClosed) :
    (symplecticForm hα hclosed).IsSymplectic := by
  rw [← (isLocalDiffeomorph_mk hα).isSymplectic_mpullback_iff (mk_surjective hα),
    mpullback_mk_symplecticForm]
  exact CotangentBundle.isSymplectic_symplecticForm

/-- **The fibres of `T*B/Λ → B` are Lagrangian.** At every point the vertical tangent space, the
kernel of the differential of the projection, is a Lagrangian subspace for the descended
symplectic form. The differential of the quotient map carries the vertical tangent space of
`T*B`, which is Lagrangian, onto it, and is a linear symplectomorphism. -/
theorem isLagrangian_ker_mfderiv_proj (hclosed : ∀ i, (α i).IsClosed) (y : LatticeQuotient α hα) :
    ((isSymplectic_symplecticForm hα hclosed).isNondegenerate.symplecticFormAt y).IsLagrangian
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (proj hα) y).ker := by
  obtain ⟨z, rfl⟩ := mk_surjective hα y
  obtain ⟨e, he⟩ := (isLocalDiffeomorph_mk hα).isInvertible_mfderiv (by simp) z
  have hsymp :
      (CotangentBundle.isSymplectic_symplecticForm.isNondegenerate.symplecticFormAt z).transport
        e.toLinearEquiv =
      (isSymplectic_symplecticForm hα hclosed).isNondegenerate.symplecticFormAt (mk hα z) := by
    rw [← SymplecticForm.isSymplectomorphism_iff_transport_eq,
      SymplecticForm.isSymplectomorphism_iff]
    intro v w
    rw [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      ← mpullback_mk_symplecticForm hα hclosed, SmoothForm.eval₂_mpullback,
      ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe, he]
  have hcomp : mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I B → B) z =
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (proj hα) (mk hα z)).comp (e : _ →L[ℝ] _) := by
    rw [he, ← proj_comp_mk hα]
    exact mfderiv_comp z ((contMDiff_proj hα).mdifferentiableAt (by simp))
      ((contMDiff_mk hα).mdifferentiableAt (by simp))
  have hker : (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (proj hα) (mk hα z)).ker =
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I B → B) z).ker.map
        e.toLinearEquiv.toLinearMap := by
    refine (Submodule.map_comap_eq_of_surjective e.surjective _).symm.trans (congrArg _ ?_)
    rw [← LinearMap.ker_comp]
    exact congrArg (fun f : _ →L[ℝ] _ ↦ f.toLinearMap.ker) hcomp.symm
  rw [hker, ← hsymp, SymplecticForm.isLagrangian_map_transport_iff]
  exact CotangentBundle.isLagrangian_ker_mfderiv_proj z

/-- **`T*B/Λ → B` is a regular Lagrangian torus fibration** for the descended symplectic form: a
proper submersion with connected Lagrangian fibres. It is the model torus bundle of the period
lattice spanned by a closed coframe. -/
theorem isLagrangianTorusFibration_proj (hclosed : ∀ i, (α i).IsClosed) :
    (isSymplectic_symplecticForm hα hclosed).isNondegenerate.IsLagrangianTorusFibration I
      (proj hα) where
  isSubmersion := (isSubmersionOfComplement_proj hα).isSubmersion
  isLagrangian_ker_mfderiv := isLagrangian_ker_mfderiv_proj hα hclosed
  isProperMap := isProperMap_proj hα
  isConnected_preimage_singleton := isConnected_proj_preimage_singleton hα

/-! ### Lagrangian sections -/

/-- The section `x ↦ [β x]` of `T*B/Λ` defined by a one-form `β` pulls the descended symplectic
form back to `-dβ`. -/
theorem mpullback_mk_comp_section_symplecticForm (hclosed : ∀ i, (α i).IsClosed)
    (β : SmoothForm I B ℝ 1) :
    SmoothForm.mpullback
        (fun x ↦ mk hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x)))
        ((contMDiff_mk hα).comp (SmoothForm.degreeOneEquiv β).contMDiff)
        (symplecticForm hα hclosed) =
      -mextDerivₗ I 1 β := by
  rw [← mpullback_symplecticForm β, ← mpullback_mk_symplecticForm hα hclosed,
    SmoothForm.mpullback_mpullback]
  rfl

/-- **Lagrangian sections.** The section `x ↦ [β x]` of `T*B/Λ` defined by a one-form `β` is a
Lagrangian map exactly when `β` is closed. In particular the zero section of `T*B` descends to a
Lagrangian section of `T*B/Λ`. -/
theorem isLagrangianMap_mk_comp_section_iff (hclosed : ∀ i, (α i).IsClosed)
    (β : SmoothForm I B ℝ 1) :
    (isSymplectic_symplecticForm hα hclosed).isNondegenerate.IsLagrangianMap I
        (fun x ↦ mk hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x))) ↔
      β.IsClosed := by
  have hs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x ↦ mk hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x))) :=
    (contMDiff_mk hα).comp (SmoothForm.degreeOneEquiv β).contMDiff
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, ← neg_eq_zero,
      ← mpullback_mk_comp_section_symplecticForm hα hclosed β]
    exact (SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero hs).1
      h.isIsotropicMap
  refine SmoothTwoForm.IsNondegenerate.IsIsotropicMap.isLagrangianMap_of_finrank
    ((SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero hs).2 ?_)
    (fun x ↦ ?_) ?_
  · rw [mpullback_mk_comp_section_symplecticForm hα hclosed,
      (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero β).1 h, neg_zero]
  · -- The projection `T*B/Λ → B` is a left inverse of the section.
    exact mfderiv_injective_of_leftInverse ((contMDiff_proj hα _).mdifferentiableAt (by simp))
      ((hs x).mdifferentiableAt (by simp)) fun _ ↦ proj_mk hα _
  · rw [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq, two_mul]

end Manifold

end LatticeQuotient

end CotangentBundle

end TauCeti
