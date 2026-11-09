/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import TauCeti.Analysis.Normed.Group.Int
public import TauCeti.Geometry.Manifold.DifferentialForm.Quotient
public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Topology.FiberBundle.Countable
public import TauCeti.Topology.FiberBundle.Separation

/-!
# The cotangent bundle modulo a period lattice

Let `B` be a smooth manifold and let `α₁, …, αₙ` be smooth one-forms on `B` forming a global
frame of the cotangent bundle: at every point `x` the covectors `αᵢ(x)` are a basis of `T*_x B`.
They span a lattice `Λ_x = ∑ᵢ ℤ αᵢ(x)` in every fibre, and `ℤⁿ` acts on `T*B` by fibrewise
translation along these lattices,

`k • (x, p) = (x, p + ∑ᵢ kᵢ αᵢ(x))`.

This file proves that the action is free and properly discontinuous, so that its orbit space
`T*B / Λ` (`TauCeti.CotangentBundle.LatticeQuotient α hα`) is a smooth manifold whose orbit
projection is a local diffeomorphism. The projection `T*B / Λ → B` is smooth and proper, and its
fibre over `x` is the compact torus `T*_x B / Λ_x`.

Fibrewise translation by a one-form `β` pulls the canonical symplectic form `ω = -dλ` back to
`ω - π^* dβ` (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm`).
So when every `αᵢ` is closed, `ℤⁿ` acts by symplectomorphisms and `ω` descends to a symplectic
form on `T*B / Λ` (`TauCeti.CotangentBundle.LatticeQuotient.symplecticForm`). The Liouville form
does not descend: translation by `∑ᵢ kᵢ αᵢ` changes it by `π^* (∑ᵢ kᵢ αᵢ)`. The section of
`T*B / Λ` defined by a one-form `β` is Lagrangian exactly when `β` is closed; in particular the
zero section descends to a Lagrangian section.

This is the canonical model `T*B / Λ` of a Lagrangian torus fibration whose period lattice
`Λ ⊂ T*B` is spanned by global closed one-forms. The coordinate time forms of a torus give an
example (`TauCeti.CotangentBundle.isLocalFrameOn_torusTimeForm`).

Freeness and proper discontinuity come from a continuous equivariant coordinate map: read in the
trivialization of `T*B` defined by the frame (`IsLocalFrameOn.trivialization`), a covector has
coordinates in `ℝⁿ`, and translating by `k` adds `k` to them.

## Main definitions

* `TauCeti.CotangentBundle.latticeForm α k`: the one-form `∑ᵢ kᵢ αᵢ` for `k ∈ ℤⁿ`.
* `TauCeti.CotangentBundle.LatticeQuotient.Cover α hα`: a type synonym of `T*B` carrying the
  translation action of `Multiplicative (ι → ℤ)`.
* `TauCeti.CotangentBundle.LatticeQuotient α hα`: the orbit space `T*B / Λ`.
* `TauCeti.CotangentBundle.LatticeQuotient.mk`, `TauCeti.CotangentBundle.LatticeQuotient.proj`:
  the orbit projection `T*B → T*B / Λ` and the projection `T*B / Λ → B`.
* `TauCeti.CotangentBundle.LatticeQuotient.symplecticForm`: the symplectic form descended from
  the canonical symplectic form of `T*B`, for a frame of closed one-forms.

## Main results

* `TauCeti.CotangentBundle.isLocalFrameOn_degreeOneEquiv_univ_iff`: one-forms are a global frame
  of `T*B` exactly when their values are a basis of every cotangent space.
* `TauCeti.CotangentBundle.LatticeQuotient.Cover.instIsCancelSMul`,
  `TauCeti.CotangentBundle.LatticeQuotient.Cover.instProperlyDiscontinuousSMul`: the translation
  action is free and properly discontinuous.
* `TauCeti.CotangentBundle.LatticeQuotient.isLocalDiffeomorph_mk`: the orbit projection is a smooth
  local diffeomorphism.
* `TauCeti.CotangentBundle.LatticeQuotient.mk_eq_mk_iff`: two covectors have the same class exactly
  when they lie over the same point and differ by a lattice vector.
* `TauCeti.CotangentBundle.LatticeQuotient.contMDiff_proj`,
  `TauCeti.CotangentBundle.LatticeQuotient.isProperMap_proj`: the projection to `B` is smooth and
  proper, so its fibres are compact.
* `TauCeti.CotangentBundle.LatticeQuotient.mpullback_mk_symplecticForm`,
  `TauCeti.CotangentBundle.LatticeQuotient.isSymplectic_symplecticForm`: the descended form pulls
  back to `ω` and is symplectic.
* `TauCeti.CotangentBundle.LatticeQuotient.isLagrangianMap_mk_comp_section_iff`: the section
  defined by a one-form is Lagrangian exactly when the form is closed.
* `TauCeti.CotangentBundle.isLocalFrameOn_torusTimeForm`: the coordinate time forms of a torus are
  a global frame of its cotangent bundle.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. **33** (1980),
  687–706 (the torus bundle `T*B / Λ` of a period lattice).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public noncomputable section

open Bundle Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [IsManifold I ∞ B] {ι : Type*}

/-! ### Global coframes -/

/-- One-forms form a global frame of the cotangent bundle exactly when their values form a basis
of every cotangent space: smoothness of the frame is automatic. -/
theorem isLocalFrameOn_degreeOneEquiv_univ_iff {α : ι → SmoothForm I B ℝ 1} :
    IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i ↦ ⇑(SmoothForm.degreeOneEquiv (α i))) univ ↔
      ∀ x : B, LinearIndependent ℝ (fun i ↦ SmoothForm.degreeOneEquiv (α i) x) ∧
        ⊤ ≤ Submodule.span ℝ (range fun i ↦ SmoothForm.degreeOneEquiv (α i) x) :=
  ⟨fun h x ↦ ⟨h.linearIndependent (mem_univ x), h.generating (mem_univ x)⟩, fun h ↦
    { linearIndependent := fun {x} _ ↦ (h x).1
      generating := fun {x} _ ↦ (h x).2
      contMDiffOn := fun i ↦ (SmoothForm.degreeOneEquiv (α i)).contMDiff.contMDiffOn }⟩

/-! ### Lattice one-forms -/

section LatticeForm

variable [Fintype ι] (α : ι → SmoothForm I B ℝ 1)

/-- The one-form `∑ᵢ kᵢ αᵢ` for an integer vector `k`. Its values are the vectors of the lattices
spanned by the covectors `αᵢ(x)`. -/
def latticeForm (k : ι → ℤ) : SmoothForm I B ℝ 1 :=
  ∑ i, k i • α i

/-- The zero integer vector gives the zero one-form. -/
@[simp]
theorem latticeForm_zero : latticeForm α 0 = 0 := by
  simp [latticeForm]

/-- The lattice one-form is additive in the integer vector. -/
theorem latticeForm_add (k l : ι → ℤ) :
    latticeForm α (k + l) = latticeForm α k + latticeForm α l := by
  simp [latticeForm, add_smul, Finset.sum_add_distrib]

/-- The value of `∑ᵢ kᵢ αᵢ` at `x`, as a covector, is `∑ᵢ kᵢ αᵢ(x)`. -/
theorem degreeOneEquiv_latticeForm_apply (k : ι → ℤ) (x : B) :
    SmoothForm.degreeOneEquiv (latticeForm α k) x =
      ∑ i, k i • SmoothForm.degreeOneEquiv (α i) x := by
  simp only [latticeForm, map_sum, map_zsmul]
  rw [← ContMDiffSection.coeAddHom_apply, map_sum]
  simp [ContMDiffSection.coe_zsmul]

variable {α} in
/-- An integer combination of closed one-forms is closed. -/
theorem isClosed_latticeForm (hα : ∀ i, (α i).IsClosed) (k : ι → ℤ) :
    (latticeForm α k).IsClosed :=
  Finset.sum_induction _ SmoothForm.IsClosed (fun _ _ ↦ SmoothForm.IsClosed.add)
    SmoothForm.isClosed_zero fun i _ ↦ (hα i).smul (k i)

end LatticeForm

variable (α : ι → SmoothForm I B ℝ 1)
  (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i ↦ ⇑(SmoothForm.degreeOneEquiv (α i))) univ)

/-! ### The translation action -/

/-- The cotangent bundle `T*B`, as a type synonym carrying the action of `Multiplicative (ι → ℤ)`
by translation along the lattices spanned by a global frame `α` of one-forms,
`k • (x, p) = (x, p + ∑ᵢ kᵢ αᵢ(x))`. -/
@[expose] def LatticeQuotient.Cover
    (_α : ι → SmoothForm I B ℝ 1)
    (_hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i ↦ ⇑(SmoothForm.degreeOneEquiv (_α i))) univ) :
    Type _ :=
  CotangentBundle I B

namespace LatticeQuotient.Cover

instance : TopologicalSpace (Cover α hα) := inferInstanceAs (TopologicalSpace (CotangentBundle I B))

instance [T2Space B] : T2Space (Cover α hα) := inferInstanceAs (T2Space (CotangentBundle I B))

instance : ChartedSpace (ModelProd H (E →L[ℝ] ℝ)) (Cover α hα) :=
  inferInstanceAs (ChartedSpace (ModelProd H (E →L[ℝ] ℝ)) (CotangentBundle I B))

instance : IsManifold (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (Cover α hα) :=
  inferInstanceAs (IsManifold (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (CotangentBundle I B))

instance [FiniteDimensional ℝ E] : LocallyCompactSpace (Cover α hα) :=
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace (ModelProd H (E →L[ℝ] ℝ)) :=
    inferInstanceAs (LocallyCompactSpace (H × (E →L[ℝ] ℝ)))
  ChartedSpace.locallyCompactSpace (ModelProd H (E →L[ℝ] ℝ)) (CotangentBundle I B)

instance [SecondCountableTopology B] [FiniteDimensional ℝ E] :
    SecondCountableTopology (Cover α hα) :=
  inferInstanceAs (SecondCountableTopology (CotangentBundle I B))

/-- The identification of the cotangent bundle with the cover. -/
def of : CotangentBundle I B ≃ Cover α hα := Equiv.refl _

/-- The identification of the cotangent bundle with the cover is continuous. -/
theorem continuous_of : Continuous (of α hα) := continuous_id

/-- The identification of the cover with the cotangent bundle is continuous. -/
theorem continuous_of_symm : Continuous (of α hα).symm := continuous_id

/-- The identification of the cotangent bundle with the cover is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of :
    IsLocalDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (of α hα) :=
  (Diffeomorph.refl (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I B) ∞).isLocalDiffeomorph

variable [Fintype ι]

/-- Translation by the integer vector `k`, read on the cover. -/
instance : SMul (Multiplicative (ι → ℤ)) (Cover α hα) where
  smul k z := of α hα (vectorBundleTranslateDiffeomorph
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd))
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff ((of α hα).symm z))

/-- The translation by `k` is the fibrewise translation by the one-form `∑ᵢ kᵢ αᵢ`. -/
theorem smul_def (k : Multiplicative (ι → ℤ)) (z : Cover α hα) :
    k • z = of α hα (vectorBundleTranslateDiffeomorph
      (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd))
      (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff ((of α hα).symm z)) :=
  (rfl)

/-- The integer vector `k` translates a covector `p` over `x` to `p + ∑ᵢ kᵢ αᵢ(x)`. -/
theorem smul_of (k : Multiplicative (ι → ℤ)) (z : CotangentBundle I B) :
    k • of α hα z =
      of α hα ⟨z.proj, z.2 + ∑ i, k.toAdd i • SmoothForm.degreeOneEquiv (α i) z.proj⟩ := by
  rw [smul_def, Equiv.symm_apply_apply, vectorBundleTranslateDiffeomorph_apply,
    degreeOneEquiv_latticeForm_apply]

/-- `Multiplicative (ι → ℤ)` acts on the cover by fibrewise translation along the lattices. -/
instance : MulAction (Multiplicative (ι → ℤ)) (Cover α hα) where
  one_smul z := by
    obtain ⟨z, rfl⟩ := (of α hα).surjective z
    rw [smul_of]
    simp
  mul_smul j k z := by
    obtain ⟨z, rfl⟩ := (of α hα).surjective z
    rw [smul_of, smul_of, smul_of]
    refine congrArg (fun v ↦ of α hα (TotalSpace.mk' (E →L[ℝ] ℝ) z.proj v)) ?_
    simp only [toAdd_mul, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel

/-- The action is by `C^∞` maps. -/
instance instContMDiffConstSMul :
    ContMDiffConstSMul (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (Multiplicative (ι → ℤ)) (Cover α hα) where
  contMDiff_const_smul k := (vectorBundleTranslateDiffeomorph
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd))
    (SmoothForm.degreeOneEquiv (latticeForm α k.toAdd)).contMDiff).contMDiff

variable {α} in
/-- For a frame of closed one-forms, translation along the lattices preserves the canonical
symplectic form of the cotangent bundle. -/
theorem mpullback_smul_symplecticForm (hcl : ∀ i, (α i).IsClosed)
    (k : Multiplicative (ι → ℤ)) :
    SmoothForm.mpullback (k • · : Cover α hα → Cover α hα)
        (contMDiff_const_smul (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (n := ∞) k)
        (CotangentBundle.symplecticForm I B) =
      CotangentBundle.symplecticForm I B :=
  (mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff _).2
    (isClosed_latticeForm hcl k.toAdd)

/-- The action is by homeomorphisms. -/
instance : ContinuousConstSMul (Multiplicative (ι → ℤ)) (Cover α hα) where
  continuous_const_smul k := (contMDiff_const_smul (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (n := ∞)
    (M := Cover α hα) k).continuous

/-- **Equivariant coordinates.** There is a continuous map `c` from the cover to `ℝ^ι` that turns
the translation by `k` into the translation by `k`: the coordinates of a covector in the frame `α`,
read in the trivialization of `T*B` defined by the frame. Together with the base point, these
coordinates identify `T*B` with `B × ℝ^ι`, so the covectors over a compact set with coordinates in
a compact set form a compact set. -/
private theorem exists_continuous_coord : ∃ c : Cover α hα → ι → ℝ, Continuous c ∧
    (∀ (k : Multiplicative (ι → ℤ)) z, c (k • z) = c z + fun i ↦ (k.toAdd i : ℝ)) ∧
    ∀ {K : Set B} {C : Set (ι → ℝ)}, IsCompact K → IsCompact C →
      IsCompact {z : Cover α hα | ((of α hα).symm z).proj ∈ K ∧ c z ∈ C} := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨x₀⟩⟩
  · have : IsEmpty (Cover α hα) := ⟨fun z ↦ hB.false z.proj⟩
    exact ⟨isEmptyElim, continuous_of_discreteTopology, fun _ z ↦ isEmptyElim z,
      fun _ _ ↦ Set.Finite.isCompact (Set.toFinite _)⟩
  -- A basis of the model fibre, indexed by `ι`: the frame at any point.
  let b : Module.Basis ι ℝ (E →L[ℝ] ℝ) := hα.toBasisAt (mem_univ x₀)
  have : FiniteDimensional ℝ (E →L[ℝ] ℝ) := b.finiteDimensional_of_finite
  let e := hα.trivialization isOpen_univ b
  have he : ∀ z : CotangentBundle I B, e z = (z.proj, (hα.toBasisAt (mem_univ z.proj)).equiv b
      (Equiv.refl ι) z.2) := fun z ↦
    IsLocalFrameOn.trivialization_apply hα isOpen_univ b (mem_univ z.proj) z.2
  have hsrc : e.source = univ := by
    rw [e.source_eq, IsLocalFrameOn.baseSet_trivialization, preimage_univ]
  have htgt : e.target = univ := by
    rw [e.target_eq, IsLocalFrameOn.baseSet_trivialization, univ_prod_univ]
  let h := e.toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv hsrc htgt
  let L := b.equivFun.toContinuousLinearEquiv
  refine ⟨fun z ↦ L (h ((of α hα).symm z)).2, ?_, fun k z ↦ ?_, fun {K C} hK hC ↦ ?_⟩
  · exact L.continuous.comp (continuous_snd.comp (h.continuous.comp (continuous_of_symm α hα)))
  · -- The coordinate change carries the frame at every point to the basis `b`.
    have hb : ∀ (x : B) (i : ι), (hα.toBasisAt (mem_univ x)).equiv b (Equiv.refl ι)
        (SmoothForm.degreeOneEquiv (α i) x) = b i := fun x i ↦ by
      rw [← IsLocalFrameOn.toBasisAt_coe hα (mem_univ x) i, Module.Basis.equiv_apply,
        Equiv.refl_apply]
    obtain ⟨z, rfl⟩ := (of α hα).surjective z
    rw [smul_of]
    simp only [h, OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_apply,
      Trivialization.coe_coe, Equiv.symm_apply_apply, he, map_add, map_sum, map_zsmul, hb, L,
      LinearEquiv.coe_toContinuousLinearEquiv']
    ext i
    simp only [Pi.add_apply, add_right_inj]
    simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finset.sum_apply]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Finsupp.single_eq_of_ne' hj]) (by simp)]
    simp
  · -- The set is the image of the compact set `K × L⁻¹(C)` under the inverse trivialization.
    convert ((h.isCompact_preimage.2 (hK.prod (L.toHomeomorph.isCompact_preimage.2 hC))).image
      (continuous_of α hα)) using 1
    ext z
    obtain ⟨z, rfl⟩ := (of α hα).surjective z
    simp only [mem_ofPred_eq, mem_image, mem_preimage, mem_prod,
      EmbeddingLike.apply_eq_iff_eq, exists_eq_right, Equiv.symm_apply_apply]
    simp [h, he]

/-- The action is free: a nontrivial integer vector translates the frame coordinates. -/
instance instIsCancelSMul : IsCancelSMul (Multiplicative (ι → ℤ)) (Cover α hα) where
  left_cancel' k _ _ h := smul_left_cancel k h
  right_cancel' j k z h := by
    obtain ⟨c, -, hc, -⟩ := exists_continuous_coord α hα
    have h' := congrArg c h
    rw [hc, hc, add_right_inj] at h'
    exact Multiplicative.toAdd.injective (funext fun i ↦ by exact_mod_cast congrFun h' i)

/-- The action is properly discontinuous: only finitely many integer vectors translate a compact
set to meet another compact set. -/
instance instProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul (Multiplicative (ι → ℤ)) (Cover α hα) where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨c, hcont, hc, -⟩ := exists_continuous_coord α hα
    -- If `k • z ∈ L` for some `z ∈ K`, then `k` is the difference of the coordinates of a point of
    -- `L` and a point of `K`, which lies in a bounded set.
    obtain ⟨R, hR⟩ := ((hL.prod hK).image ((hcont.comp continuous_fst).sub
      (hcont.comp continuous_snd))).isBounded.exists_norm_le
    have hball := (isCompact_closedBall (0 : ι → ℤ) R).finite_of_discrete
    refine (hball.preimage Multiplicative.toAdd.injective.injOn).subset fun k hk ↦ ?_
    obtain ⟨_, ⟨z, hz, rfl⟩, hkz⟩ := hk
    have h : ‖c (k • z) - c z‖ ≤ R := hR _ ⟨(k • z, z), ⟨hkz, hz⟩, rfl⟩
    rw [hc, add_sub_cancel_left] at h
    rw [mem_preimage, mem_closedBall_zero_iff, ← pi_norm_intCast_real]
    exact h

end LatticeQuotient.Cover

/-! ### The orbit space -/

variable [Fintype ι]

/-- The cotangent bundle modulo a period lattice: the orbit space `T*B / Λ` of the translation
action of `Multiplicative (ι → ℤ)` along the lattices `Λ_x = ∑ᵢ ℤ αᵢ(x)` spanned by a global frame
`α` of one-forms. Its fibre over `x` is the torus `T*_x B / Λ_x`. -/
abbrev LatticeQuotient : Type _ :=
  MulAction.orbitRel.Quotient (Multiplicative (ι → ℤ)) (LatticeQuotient.Cover α hα)

namespace LatticeQuotient

open Cover

/-- `T*B / Λ` is second countable when `B` is. -/
instance [SecondCountableTopology B] [FiniteDimensional ℝ E] :
    SecondCountableTopology (LatticeQuotient α hα) :=
  ContinuousConstSMul.secondCountableTopology

/-- The class of a covector in `T*B / Λ`. -/
def mk (z : CotangentBundle I B) : LatticeQuotient α hα :=
  Quotient.mk _ (of α hα z)

/-- Every point of `T*B / Λ` is the class of a covector. -/
theorem mk_surjective : Surjective (mk α hα) := fun y ↦ by
  obtain ⟨w, rfl⟩ := Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := (of α hα).surjective w
  exact ⟨z, rfl⟩

/-- Two covectors have the same class in `T*B / Λ` exactly when they lie over the same point and
differ by a vector of the lattice spanned by the frame there. -/
theorem mk_eq_mk_iff {z w : CotangentBundle I B} :
    mk α hα z = mk α hα w ↔
      ∃ k : ι → ℤ, z = ⟨w.proj, w.2 + ∑ i, k i • SmoothForm.degreeOneEquiv (α i) w.proj⟩ := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨k.toAdd, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨Multiplicative.ofAdd k, ?_⟩⟩
  · rw [smul_of] at hk
    exact (of α hα).injective hk.symm
  · rw [smul_of, hk]
    rfl

/-- The class of a covector `p` over `x` is unchanged by adding a lattice vector at `x`. -/
theorem mk_add_sum_zsmul (z : CotangentBundle I B) (k : ι → ℤ) :
    mk α hα ⟨z.proj, z.2 + ∑ i, k i • SmoothForm.degreeOneEquiv (α i) z.proj⟩ = mk α hα z :=
  (mk_eq_mk_iff α hα).2 ⟨k, rfl⟩

/-- Translation along the lattices preserves the base point. -/
theorem proj_of_symm_smul (k : Multiplicative (ι → ℤ)) (z : Cover α hα) :
    ((of α hα).symm (k • z)).proj = ((of α hα).symm z).proj := by
  obtain ⟨z, rfl⟩ := (of α hα).surjective z
  rw [smul_of, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The projection `T*B / Λ → B`, descended from the projection of the cotangent bundle. -/
def proj : LatticeQuotient α hα → B :=
  Quotient.lift (fun z : Cover α hα ↦ ((of α hα).symm z).proj) fun z w ⟨k, hk⟩ ↦ by
    rw [← hk]
    exact proj_of_symm_smul α hα k w

/-- The projection of the class of a covector is its base point. -/
@[simp]
theorem proj_mk (z : CotangentBundle I B) : proj α hα (mk α hα z) = z.proj :=
  (rfl)

/-- The projection `T*B / Λ → B` composed with the orbit projection is the projection of the
cotangent bundle. -/
theorem proj_comp_mk : proj α hα ∘ mk α hα = TotalSpace.proj :=
  (rfl)

/-- The projection `T*B / Λ → B` is continuous. -/
theorem continuous_proj : Continuous (proj α hα) :=
  continuous_quot_lift _
    ((FiberBundle.continuous_proj (E →L[ℝ] ℝ) _).comp (continuous_of_symm α hα))

/-- The projection `T*B / Λ → B` is surjective. -/
theorem proj_surjective : Surjective (proj α hα) := fun x ↦
  ⟨mk α hα (zeroSection (E →L[ℝ] ℝ) (fun x : B ↦ TangentSpace I x →L[ℝ] ℝ) x), rfl⟩

variable [FiniteDimensional ℝ E] [T2Space B]

/-- The orbit projection `T*B → T*B / Λ` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_mk :
    IsLocalDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (mk α hα) :=
  isLocalDiffeomorph_quotientMk (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (n := ∞) (M := Cover α hα)
    (G := Multiplicative (ι → ℤ))

/-- The orbit projection `T*B → T*B / Λ` is smooth. -/
theorem contMDiff_mk :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (mk α hα) :=
  (isLocalDiffeomorph_mk α hα).contMDiff

/-- The projection `T*B / Λ → B` is smooth. -/
theorem contMDiff_proj : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I ∞ (proj α hα) :=
  (IsLocalDiffeomorph.contMDiff_comp_iff (isLocalDiffeomorph_mk α hα) (mk_surjective α hα)
    le_rfl).1 (Bundle.contMDiff_proj (fun x : B ↦ TangentSpace I x →L[ℝ] ℝ))

/-- **The fibres are compact.** The projection `T*B / Λ → B` is a proper map: in the frame
coordinates, every class over a compact set `K` has a representative over `K` with coordinates in
the unit cube. In particular each fibre `T*_x B / Λ_x` is a compact torus. -/
theorem isProperMap_proj : IsProperMap (proj α hα) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace B := ChartedSpace.locallyCompactSpace H B
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_proj α hα, fun K hK ↦ ?_⟩
  obtain ⟨c, -, hc, hcpt⟩ := exists_continuous_coord α hα
  refine ((hcpt hK (isCompact_Icc (a := 0) (b := 1))).image continuous_quot_mk).of_isClosed_subset
    (hK.isClosed.preimage (continuous_proj α hα)) fun y hy ↦ ?_
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective y
  -- Translating by the integer parts of the coordinates moves them into the unit cube.
  let k : Multiplicative (ι → ℤ) := Multiplicative.ofAdd fun i ↦ -⌊c z i⌋
  refine ⟨k • z, ⟨(proj_of_symm_smul α hα k z).symm ▸ hy, ?_⟩, Quotient.sound ⟨k, rfl⟩⟩
  rw [hc]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;>
    simp only [k, toAdd_ofAdd, Pi.add_apply, Pi.zero_apply, Pi.one_apply, Int.cast_neg,
      ← sub_eq_add_neg, Int.self_sub_floor]
  · exact Int.fract_nonneg _
  · exact (Int.fract_lt_one _).le

/-- Every fibre `T*_x B / Λ_x` of the projection `T*B / Λ → B` is compact. -/
theorem isCompact_proj_preimage_singleton (x : B) : IsCompact (proj α hα ⁻¹' {x}) :=
  (isProperMap_proj α hα).isCompact_preimage isCompact_singleton

/-! ### The symplectic form -/

variable {α} (hcl : ∀ i, (α i).IsClosed)
include hcl

/-- The symplectic form of `T*B / Λ`, for a frame `α` of closed one-forms: the descent of the
canonical symplectic form `ω = -dλ` of the cotangent bundle, which is invariant under translation
along the lattices. -/
def symplecticForm : SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (LatticeQuotient α hα) :=
  SmoothForm.descend (G := Multiplicative (ι → ℤ)) (M := Cover α hα)
    (CotangentBundle.symplecticForm I B) (Cover.mpullback_smul_symplecticForm hα hcl)

/-- The orbit projection pulls the symplectic form of `T*B / Λ` back to the canonical symplectic
form of the cotangent bundle. -/
@[simp]
theorem mpullback_mk_symplecticForm :
    SmoothForm.mpullback (mk α hα) (contMDiff_mk α hα) (symplecticForm hα hcl) =
      CotangentBundle.symplecticForm I B :=
  SmoothForm.mpullback_quotientMk_descend (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (M := Cover α hα)
    (G := Multiplicative (ι → ℤ))

/-- The symplectic form of `T*B / Λ` is the unique two-form pulling back to the canonical
symplectic form of the cotangent bundle along the orbit projection. -/
theorem eq_symplecticForm_iff {σ : SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (LatticeQuotient α hα)} :
    σ = symplecticForm hα hcl ↔
      SmoothForm.mpullback (mk α hα) (contMDiff_mk α hα) σ = CotangentBundle.symplecticForm I B :=
  SmoothForm.eq_descend_iff (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (M := Cover α hα)
    (G := Multiplicative (ι → ℤ))

/-- The symplectic form of `T*B / Λ` is closed and nondegenerate. -/
theorem isSymplectic_symplecticForm : (symplecticForm hα hcl).IsSymplectic := by
  rw [← (isLocalDiffeomorph_mk α hα).isSymplectic_mpullback_iff (mk_surjective α hα)]
  exact (mpullback_mk_symplecticForm hα hcl).symm ▸ CotangentBundle.isSymplectic_symplecticForm

/-! ### Lagrangian sections -/

/-- The section `x ↦ [β(x)]` of `T*B / Λ` defined by a one-form `β` pulls the symplectic form back
to `-dβ`. -/
theorem mpullback_mk_comp_section_symplecticForm (β : SmoothForm I B ℝ 1) :
    SmoothForm.mpullback
        (fun x ↦ mk α hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x)))
        ((contMDiff_mk α hα).comp (SmoothForm.degreeOneEquiv β).contMDiff)
        (symplecticForm hα hcl) =
      -mextDerivₗ I 1 β := by
  rw [← mpullback_symplecticForm β, ← mpullback_mk_symplecticForm hα hcl,
    SmoothForm.mpullback_mpullback]
  rfl

/-- **Lagrangian sections.** The section `x ↦ [β(x)]` of `T*B / Λ` defined by a one-form `β` is a
Lagrangian map exactly when `β` is closed. In particular the zero section of `T*B` descends to a
Lagrangian section of `T*B / Λ`. -/
theorem isLagrangianMap_mk_comp_section_iff (β : SmoothForm I B ℝ 1) :
    (isSymplectic_symplecticForm hα hcl).isNondegenerate.IsLagrangianMap I
        (fun x ↦ mk α hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x))) ↔
      β.IsClosed := by
  have hs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x ↦ mk α hα (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x))) :=
    (contMDiff_mk α hα).comp (SmoothForm.degreeOneEquiv β).contMDiff
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, ← neg_eq_zero,
      ← mpullback_mk_comp_section_symplecticForm hα hcl β]
    exact (SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero hs).1
      h.isIsotropicMap
  refine SmoothTwoForm.IsNondegenerate.IsIsotropicMap.isLagrangianMap_of_finrank
    ((SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero hs).2 ?_)
    (fun x ↦ ?_) ?_
  · rw [mpullback_mk_comp_section_symplecticForm hα hcl,
      (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero β).1 h, neg_zero]
  · -- The projection `T*B / Λ → B` is a left inverse of the section.
    exact mfderiv_injective_of_leftInverse ((contMDiff_proj α hα _).mdifferentiableAt (by simp))
      ((hs x).mdifferentiableAt (by simp)) fun _ ↦ rfl
  · rw [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq, two_mul]

end LatticeQuotient

/-! ### Example: the cotangent bundle of a torus -/

section Torus

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The coordinate time forms `dt_i` of the torus `∀ i, AddCircle (p i)` form a global frame of its
cotangent bundle: at every point they are the coordinate functionals of `ι → ℝ`. Since they are
closed, `T*Tⁿ / Λ` for the lattice they span carries the symplectic form
`TauCeti.CotangentBundle.LatticeQuotient.symplecticForm`; for `ι = Unit` this is the torus
`T*S¹ / Λ` fibred over the circle. -/
theorem isLocalFrameOn_torusTimeForm :
    IsLocalFrameOn (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ((ι → ℝ) →L[ℝ] ℝ) ∞
      (fun i ↦ ⇑(SmoothForm.degreeOneEquiv (torusTimeForm p i))) univ := by
  classical
  -- At every point the frame is the family of coordinate functionals of `ι → ℝ`.
  have hproj : ∀ (x : ∀ i, AddCircle (p i)) (i : ι),
      SmoothForm.degreeOneEquiv (torusTimeForm p i) x = ContinuousLinearMap.proj i :=
    fun x i ↦ ContinuousLinearMap.ext fun v ↦ by
      rw [SmoothForm.degreeOneEquiv_apply_apply, torusTimeForm_apply]
      rfl
  -- The coordinate functionals of `ι → ℝ` are linearly independent and span its dual.
  have hli : LinearIndependent ℝ fun i ↦ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) :=
    Fintype.linearIndependent_iff.2 fun c hc j ↦ by
      simpa [Pi.single_apply] using congrArg (fun f : (ι → ℝ) →L[ℝ] ℝ ↦ f (Pi.single j 1)) hc
  have hspan : ⊤ ≤ Submodule.span ℝ
      (range fun i ↦ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
    rintro f -
    -- A functional is the combination of the coordinate functionals with its values on the
    -- standard basis vectors.
    have hf : f = ∑ i, f (Pi.single i 1) • ContinuousLinearMap.proj i := by
      refine ContinuousLinearMap.ext fun v ↦ ?_
      have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
        ext j
        simp [Pi.single_apply]
      conv_lhs => rw [hv]
      simp [map_sum, mul_comm]
    rw [hf]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine isLocalFrameOn_degreeOneEquiv_univ_iff.2 fun x ↦ ⟨?_, ?_⟩
  · simp only [hproj]
    exact hli
  · simp only [hproj]
    exact hspan

end Torus

end CotangentBundle

end TauCeti
