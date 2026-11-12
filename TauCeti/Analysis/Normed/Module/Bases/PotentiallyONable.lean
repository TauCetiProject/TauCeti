/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.OpenMapping
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Potentially orthonormalisable modules and property (Pr)

Let `R` be a normed ring. Besides the orthonormalisable modules `TauCeti.IsONable R M`, linearly
isometric to a model space `C₀(I, R)`, nonarchimedean functional analysis uses two weaker
conditions which only see the topology of `M`:

* `TauCeti.IsPotentiallyONable R M`: `M` is continuously linearly equivalent to some `C₀(I, R)`;
* `TauCeti.HasPr R M` (*property (Pr)*): `M` is a continuous linear retract of some `C₀(I, R)`,
  that is, there are continuous linear maps `i : M →L[R] C₀(I, R)` and `r : C₀(I, R) →L[R] M`
  with `r ∘ i = id`. Then `C₀(I, R)` is the topological direct sum of the range of `i` and the
  kernel of `r`, so this is the condition that `M` is a topological direct summand of a model
  space; Buzzard defines property (Pr) equivalently by a direct sum `M × Q` being potentially
  orthonormalisable.

Then `IsONable R M → IsPotentiallyONable R M → HasPr R M`. Both new conditions are invariant
under continuous linear equivalence, stable under finite products (using
`C₀(I ⊕ J, R) ≃ C₀(I, R) × C₀(J, R)`), and (Pr) passes to continuous linear retracts.

Over a ring with a multiplicative pseudo-uniformiser (`TauCeti.NormedRing.IsTate R`), property
(Pr) is the analytic analogue of projectivity:

* `TauCeti.HasPr.lifting_property`: every continuous linear map `f : M →L[R] F` out of a module
  with (Pr) lifts through every continuous linear surjection `q : E →L[R] F` from a complete
  ultrametric module onto a complete module. The lift is built from bounded lifts of the images
  of the coordinate vectors, which exist by the quantitative open mapping theorem.
* `TauCeti.hasPr_iff_forall_exists_comp_eq_id`: over a complete ultrametric such ring, a complete
  ultrametric module has (Pr) exactly when every continuous linear surjection onto it from a
  complete ultrametric module in `Type (max u v)` has a continuous linear section. For the
  converse, the vectors of norm at most one are the coordinate images of a surjection from a model
  space onto `M`.
* `TauCeti.HasPr.projective`: a finitely generated module with (Pr) is a continuous linear retract
  of some `R ^ n` (`TauCeti.HasPr.exists_comp_eq_id_of_finite`), so it is projective. It is complete
  by `TauCeti.HasPr.completeSpace`, since over a complete ring a retract of `C₀(I, R)` is
  complete.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois Representations*, LMS Lecture Note
  Series 320 (2007), §2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
-/

public section

open Function ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

universe u v

namespace TauCeti

section Defs

variable (R : Type*) [SeminormedRing R]

/-- A normed module is **potentially orthonormalisable** if it is continuously linearly
equivalent to a model space `C₀(I, R)` of families on a discrete index type tending to zero along
the cofinite filter. -/
def IsPotentiallyONable (M : Type u) [SeminormedAddCommGroup M] [Module R M] : Prop :=
  ∃ (I : Type u) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃L[R] C₀(I, R))

/-- A module is potentially orthonormalisable exactly when it is continuously linearly
equivalent to `C₀(I, R)` for some discrete index type `I`. This is the introduction and
elimination interface for `IsPotentiallyONable`. -/
theorem isPotentiallyONable_def (M : Type u) [SeminormedAddCommGroup M] [Module R M] :
    IsPotentiallyONable R M ↔
      ∃ (I : Type u) (_ : TopologicalSpace I) (_ : DiscreteTopology I),
        Nonempty (M ≃L[R] C₀(I, R)) :=
  Iff.rfl

/-- A normed module has **property (Pr)** if it is a continuous linear retract of a model space
`C₀(I, R)`: there are continuous linear maps `i : M →L[R] C₀(I, R)` and `r : C₀(I, R) →L[R] M`
with `r ∘ i = id`. -/
def HasPr (M : Type u) [SeminormedAddCommGroup M] [Module R M] : Prop :=
  ∃ (I : Type u) (_ : TopologicalSpace I) (_ : DiscreteTopology I)
    (i : M →L[R] C₀(I, R)) (r : C₀(I, R) →L[R] M), r.comp i = .id R M

/-- A module has property (Pr) exactly when it is a continuous linear retract of `C₀(I, R)` for
some discrete index type `I`. This is the introduction and elimination interface for `HasPr`. -/
theorem hasPr_def (M : Type u) [SeminormedAddCommGroup M] [Module R M] :
    HasPr R M ↔
      ∃ (I : Type u) (_ : TopologicalSpace I) (_ : DiscreteTopology I)
        (i : M →L[R] C₀(I, R)) (r : C₀(I, R) →L[R] M), r.comp i = .id R M :=
  Iff.rfl

end Defs

variable {R : Type v}

section Seminormed

variable [SeminormedRing R] {M N : Type u} [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N]

/-- An orthonormalisable module is potentially orthonormalisable. -/
theorem IsONable.isPotentiallyONable (h : IsONable R M) : IsPotentiallyONable R M :=
  let ⟨I, _, hI, ⟨c⟩⟩ := (isONable_def R M).1 h
  ⟨I, _, hI, ⟨c.toContinuousLinearEquiv⟩⟩

/-- A potentially orthonormalisable module has property (Pr). -/
theorem IsPotentiallyONable.hasPr (h : IsPotentiallyONable R M) : HasPr R M :=
  let ⟨I, _, hI, ⟨e⟩⟩ := h
  ⟨I, _, hI, e, e.symm, by ext; simp⟩

/-- Potential orthonormalisability is invariant under continuous linear equivalence. -/
theorem IsPotentiallyONable.of_equiv (h : IsPotentiallyONable R N) (e : M ≃L[R] N) :
    IsPotentiallyONable R M :=
  let ⟨I, _, hI, ⟨c⟩⟩ := h
  ⟨I, _, hI, ⟨e.trans c⟩⟩

/-- A continuous linear retract of a module with property (Pr) has property (Pr). -/
theorem HasPr.of_retract (h : HasPr R N) (i : M →L[R] N) (r : N →L[R] M)
    (hri : r.comp i = .id R M) : HasPr R M := by
  obtain ⟨I, _, hI, j, s, hsj⟩ := h
  refine ⟨I, _, hI, j.comp i, r.comp s, ?_⟩
  rw [ContinuousLinearMap.comp_assoc, ← s.comp_assoc, hsj, ContinuousLinearMap.id_comp, hri]

/-- Property (Pr) is invariant under continuous linear equivalence. -/
theorem HasPr.of_equiv (h : HasPr R N) (e : M ≃L[R] N) : HasPr R M :=
  h.of_retract e e.symm (by ext; simp)

/-- A finite product of potentially orthonormalisable modules is potentially orthonormalisable. -/
theorem IsPotentiallyONable.prod (hM : IsPotentiallyONable R M) (hN : IsPotentiallyONable R N) :
    IsPotentiallyONable R (M × N) :=
  let ⟨I, _, _, ⟨eM⟩⟩ := hM
  let ⟨J, _, _, ⟨eN⟩⟩ := hN
  ⟨I ⊕ J, inferInstance, inferInstance,
    ⟨(eM.prodCongr eN).trans (sumEquiv R R).symm.toContinuousLinearEquiv⟩⟩

/-- A finite product of modules with property (Pr) has property (Pr). -/
theorem HasPr.prod (hM : HasPr R M) (hN : HasPr R N) : HasPr R (M × N) := by
  obtain ⟨I, _, _, i, r, hri⟩ := hM
  obtain ⟨J, _, _, j, s, hsj⟩ := hN
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hsj' (y : N) : s (j y) = y := by simpa using DFunLike.congr_fun hsj y
  let e := (sumEquiv R R (I := I) (J := J)).toContinuousLinearEquiv
  refine ⟨I ⊕ J, inferInstance, inferInstance, (e.symm : _ →L[R] _).comp (i.prodMap j),
    (r.prodMap s).comp (e : _ →L[R] _), ?_⟩
  ext x <;> simp [hri', hsj']

/-- Over a complete ring, a module with property (Pr) is complete: a Cauchy filter on `M` maps
to a Cauchy filter on the complete model space `C₀(I, R)`, whose limit the retraction sends to a
limit of the original filter. -/
theorem HasPr.completeSpace [CompleteSpace R] (h : HasPr R M) : CompleteSpace M := by
  obtain ⟨I, _, _, i, r, hri⟩ := h
  refine ⟨fun {f} hf ↦ ?_⟩
  obtain ⟨y, hy⟩ := CompleteSpace.complete (hf.map i.uniformContinuous)
  refine ⟨r y, ?_⟩
  have hri' : r ∘ i = id := funext fun x ↦ by simpa using DFunLike.congr_fun hri x
  simpa [Filter.Tendsto, hri'] using (r.continuous.tendsto y).comp hy

end Seminormed

section Lifting

variable [SeminormedRing R] [NormedRing.IsTate R] {M : Type u} [SeminormedAddCommGroup M]
  [Module R M]

/-- **Lifting property of (Pr) modules**: over a ring with a multiplicative pseudo-uniformiser,
every continuous linear map `f : M →L[R] F` out of a module with property (Pr) lifts through
every continuous linear surjection `q : E →L[R] F` from a complete ultrametric module onto a
complete module: there is `g : M →L[R] E` with `q ∘ g = f`. -/
theorem HasPr.lifting_property {E F : Type*} [NormedAddCommGroup E] [Module R E]
    [IsBoundedSMul R E] [IsUltrametricDist E] [CompleteSpace E] [NormedAddCommGroup F]
    [Module R F] [IsBoundedSMul R F] [CompleteSpace F] (h : HasPr R M) (q : E →L[R] F)
    (f : M →L[R] F) (hq : Surjective q) : ∃ g : M →L[R] E, q.comp g = f := by
  classical
  obtain ⟨I, _, _, i, r, hri⟩ := h
  -- Lift the images of the coordinate vectors under `f ∘ r` with a uniform bound; they are
  -- bounded, so the lifts are bounded and define a continuous linear map out of `C₀(I, R)`.
  obtain ⟨C, hC, hlift⟩ := q.exists_preimage_norm_le_of_isTate hq
  choose x hqx hx using fun j : I ↦ hlift (f (r (single j 1)))
  obtain ⟨B, hB⟩ := memℓp_infty_iff.1 (memℓp_infty_apply_single (f.comp r))
  have hxb : Memℓp x ⊤ := memℓp_infty ⟨C * B, by
    rintro _ ⟨j, rfl⟩
    exact (hx j).trans (mul_le_mul_of_nonneg_left (hB ⟨j, rfl⟩) hC.le)⟩
  have hg : q.comp (linearCombination R ⟨x, hxb⟩) = f.comp r :=
    continuousLinearMap_ext_single_one fun j ↦ by simp [linearCombination_single, hqx]
  refine ⟨(linearCombination R ⟨x, hxb⟩).comp i, ?_⟩
  rw [← ContinuousLinearMap.comp_assoc, hg, ContinuousLinearMap.comp_assoc, hri,
    ContinuousLinearMap.comp_id]

end Lifting

section Splitting

variable [NormedRing R] [NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]
  {M : Type u} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **Property (Pr) is the splitting of surjections**: over a complete ultrametric ring with a
multiplicative pseudo-uniformiser, a complete ultrametric module `M` has property (Pr) exactly
when every continuous linear surjection `q : E →L[R] M` from a complete ultrametric module `E` in
`Type (max u v)` has a continuous linear section. This universe suffices because the converse only
uses the model space `C₀({x : M // ‖x‖ ≤ 1}, R)`; for sources in arbitrary universes, the forward
direction is `HasPr.lifting_property`. -/
theorem hasPr_iff_forall_exists_comp_eq_id [CompleteSpace M] [IsUltrametricDist M] :
    HasPr R M ↔ ∀ (E : Type max u v) [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
      [IsUltrametricDist E] [CompleteSpace E] (q : E →L[R] M), Surjective q →
        ∃ s : M →L[R] E, q.comp s = .id R M := by
  classical
  refine ⟨fun h E _ _ _ _ _ q hq ↦ h.lifting_property q _ hq, fun h ↦ ?_⟩
  obtain ⟨ϖ⟩ := NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  -- The vectors of norm at most one, as a discrete index type, are the coordinate images of a
  -- surjection from a model space onto `M`.
  let B := {x : M // ‖x‖ ≤ 1}
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have hb : Memℓp (fun b : B ↦ (b : M)) ⊤ := memℓp_infty ⟨1, by rintro _ ⟨b, rfl⟩; exact b.2⟩
  set q : C₀(B, R) →L[R] M := linearCombination R ⟨_, hb⟩
  have hq : Surjective q := fun y ↦ by
    obtain rfl | hy := eq_or_ne y 0
    · exact ⟨0, map_zero q⟩
    -- Rescale `y` into the closed unit ball by a power of the pseudo-uniformiser.
    obtain ⟨n, ⟨-, hn⟩, -⟩ := ϖ.existsUnique_norm_zpow_smul_mem_Ioc (norm_ne_zero_iff.2 hy)
    exact ⟨single ⟨_, hn⟩ (((ϖ.unit ^ n)⁻¹ : Rˣ) : R), by
      simp [q, linearCombination_single, smul_smul]⟩
  obtain ⟨s, hs⟩ := h C₀(B, R) q hq
  exact ⟨B, ⊥, ⟨rfl⟩, s, q, hs⟩

/-- **Finite (Pr) modules are retracts of finite free modules**: over a complete ultrametric ring
with a multiplicative pseudo-uniformiser, a finitely generated module `M` with property (Pr) is a
continuous linear retract `r ∘ i = id` of `R ^ n` for some `n`. -/
theorem HasPr.exists_comp_eq_id_of_finite [Module.Finite R M] (h : HasPr R M) :
    ∃ (n : ℕ) (i : M →L[R] (Fin n → R)) (r : (Fin n → R) →L[R] M), r.comp i = .id R M := by
  have := h.completeSpace
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  -- The generators `v` give a continuous linear surjection `R ^ n → M`; it splits by (Pr).
  let q : (Fin n → R) →L[R] M :=
    ⟨Fintype.linearCombination R v, (Fintype.linearCombination R v).continuous_on_pi⟩
  have hq : Surjective q := (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).1 hv
  obtain ⟨s, hs⟩ := h.lifting_property q (.id R M) hq
  exact ⟨n, s, q, hs⟩

/-- **Finite (Pr) modules are projective**: over a complete ultrametric ring with a
multiplicative pseudo-uniformiser, a finitely generated module with property (Pr) is a projective
module. -/
theorem HasPr.projective [Module.Finite R M] (h : HasPr R M) : Module.Projective R M := by
  obtain ⟨n, s, q, hs⟩ := h.exists_comp_eq_id_of_finite
  exact Module.Projective.of_split s.toLinearMap q.toLinearMap
    (by rw [← ContinuousLinearMap.toLinearMap_comp, hs, ContinuousLinearMap.coe_id])

end Splitting

end TauCeti
