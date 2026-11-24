/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Sum
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Local
public import TauCeti.Topology.Algebra.Projectivization.Product

/-!
# Semialgebraic subsets of multiprojective spaces

Let `M = (i : ι) → ℙ K (κ i → K)` be a product of projective spaces over an ordered field `K`,
including the empty product (`IsEmpty ι`). Using `TauCeti.piConeDomain` and
`TauCeti.piConePreimage` from `TauCeti.LinearAlgebra.Projectivization.Product`, a subset `S ⊆ M` is
*multiprojective semialgebraic* (`TauCeti.IsMultiprojectiveSemialgebraic S`) when `piConePreimage S`
is semialgebraic in `(Σ i, κ i) → K`. For finite `ι` and finite `κ i`, these sets form an algebra of
sets closed under complements, finite Boolean operations, standard product affine opens, products,
diagonals, and singletons without projection closure. The topological properties of `piProjector`
and `piProjectorLocus` live in `TauCeti.Topology.Algebra.Projectivization.Product`.

Using `TauCeti.IsSemialgebraic.preimage_eval_div`, the first three characterizations below are
equivalent over **any** ordered field (without `HasSemialgebraicProjections K`), and over `ℝ` they
are equivalent to local chart semialgebraicity on `closure S` (and hence at every point of `M`):

1. **Cone preimage**: `piConePreimage S` is semialgebraic in `(Σ i, κ i) → K`.
2. **Embedded projector image**: `piProjectorCoords '' S` is semialgebraic in
   `(Σ i, κ i × κ i) → K`, where `piProjector` embeds `M` onto `TauCeti.piProjectorLocus κ K`.
3. **Global standard product affine charts** (finite `ι`, `κ i = Fin (n i + 1)`): for every `I`,
   `piAffineChart I '' (S ∩ piAffineOpen I)` is semialgebraic in `(Σ i, Fin (n i)) → K`.
4. **Local chart semialgebraicity** (over `ℝ` and finite `ι`): every `p ∈ closure S` (equivalently,
   every `p ∈ M`) has a chart `piAffineChart I` around `p` where the image of `S ∩ piAffineOpen I`
   is semialgebraic at `piAffineChart I p`.

## Main declarations

* `TauCeti.isSemialgebraic_piProjectorLocus`: semialgebraicity of the flattened product projector
  locus.
* `TauCeti.IsMultiprojectiveSemialgebraic` and
  `TauCeti.isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords`: cone
  definition and equivalence with the embedded projector model.
* `TauCeti.isMultiprojectiveSemialgebraic_image_piAffineChart_symm_iff`,
  `TauCeti.isMultiprojectiveSemialgebraic_piAffineOpen_inter_preimage_piAffineChart_iff`, and
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_isSemialgebraic_image_piAffineChart`:
  single-chart inverse transport and global standard product affine chart characterization.
* `TauCeti.isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt`,
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_exists_semialgebraicAt`, and
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt`: real local-to-global chart
  characterizations.
* `TauCeti.IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image` and
  `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_preimage_of_isMultiprojectiveSemialgebraic`
  (both assuming `HasSemialgebraicProjections K`), together with
  `TauCeti.isSemialgebraicOn_piProjectorCoords_comp_of_rightInvOn`: affine-to-multiprojective
  image, preimage, and right-inverse projector transport.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
  ihrer Grenzgebiete (3) 36, Springer, 1998, §3.4.

The product projector and standard product affine-chart equivalences generalize the single-factor
real projector arguments in `TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding`.
-/

public section

universe v

open Matrix MeasureTheory MvPolynomial Projectivization Set
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### Semialgebraicity of the punctured multicone and multiprojective semialgebraic sets -/

/-- For finite `ι` and finite blocks `κ i`, the flattened punctured-cone domain is semialgebraic:
each block is nonzero precisely when at least one of its coordinates is nonzero. -/
theorem isSemialgebraic_piConeDomain {ι : Type*} {κ : ι → Type*} {R : Type*}
    [CommRing R] [LinearOrder R] [Finite ι] [∀ i, Finite (κ i)] :
    IsSemialgebraic (piConeDomain κ R) := by
  convert IsSemialgebraic.iInter fun i : ι ↦ IsSemialgebraic.iUnion fun j : κ i ↦
    isSemialgebraic_eval_ne_zero (X ⟨i, j⟩ : MvPolynomial (Σ i, κ i) R) using 1
  ext v
  simp only [mem_piConeDomain_iff, Function.ne_iff, Pi.zero_apply, mem_iInter, mem_iUnion,
    Set.mem_ofPred_eq, eval_X, ne_eq]

section MultiprojectiveSemialgebraic

variable {ι : Type*} {κ : ι → Type v} {K : Type*} [Field K] [LinearOrder K]

/-- A subset `S` of a multiprojective space `(i : ι) → ℙ K (κ i → K)` is *multiprojective
semialgebraic* if its preimage `piConePreimage S` in the flattened coordinate space `(Σ i, κ i) → K`
is semialgebraic. -/
def IsMultiprojectiveSemialgebraic (S : Set ((i : ι) → ℙ K (κ i → K))) : Prop :=
  IsSemialgebraic (piConePreimage S)

theorem isMultiprojectiveSemialgebraic_def {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraic S ↔ IsSemialgebraic (piConePreimage S) := Iff.rfl

@[simp]
theorem isMultiprojectiveSemialgebraic_empty :
    IsMultiprojectiveSemialgebraic (∅ : Set ((i : ι) → ℙ K (κ i → K))) := by
  simp [IsMultiprojectiveSemialgebraic]

theorem IsMultiprojectiveSemialgebraic.union {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∪ T) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_union]; exact IsSemialgebraic.union hS hT

theorem IsMultiprojectiveSemialgebraic.inter {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∩ T) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_inter]; exact IsSemialgebraic.inter hS hT

theorem IsMultiprojectiveSemialgebraic.sdiff {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S \ T) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_sdiff]; exact IsSemialgebraic.sdiff hS hT

theorem IsMultiprojectiveSemialgebraic.iUnion {α : Type*} [Finite α]
    {S : α → Set ((i : ι) → ℙ K (κ i → K))} (hS : ∀ a, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋃ a, S a) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_iUnion]; exact IsSemialgebraic.iUnion hS

theorem IsMultiprojectiveSemialgebraic.biUnion {α : Type*} {t : Set α} (ht : t.Finite)
    {S : α → Set ((i : ι) → ℙ K (κ i → K))}
    (hS : ∀ a ∈ t, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋃ a ∈ t, S a) := by
  have := ht.to_subtype; rw [biUnion_eq_iUnion]
  exact IsMultiprojectiveSemialgebraic.iUnion fun x ↦ hS x.val x.property

/-- For finite `ι`, every standard product affine open `piAffineOpen I` is multiprojective
semialgebraic (without requiring finiteness of the factor coordinate types `κ i`). -/
theorem isMultiprojectiveSemialgebraic_piAffineOpen [Finite ι] (I : ∀ i, κ i) :
    IsMultiprojectiveSemialgebraic (piAffineOpen (K := K) I) := by
  rw [isMultiprojectiveSemialgebraic_def, piConePreimage_piAffineOpen]
  convert IsSemialgebraic.iInter fun i : ι ↦
    isSemialgebraic_eval_ne_zero (X ⟨i, I i⟩ : MvPolynomial (Σ i, κ i) K) using 1
  ext v; simp

section Finite

variable [Finite ι] [∀ i, Finite (κ i)]

/-- For finite `ι` and finite blocks `κ i`, the multiprojective semialgebraic subsets form an
algebra of sets. -/
theorem isSetAlgebra_setOf_isMultiprojectiveSemialgebraic :
    IsSetAlgebra {S : Set ((i : ι) → ℙ K (κ i → K)) | IsMultiprojectiveSemialgebraic S} where
  empty_mem := isMultiprojectiveSemialgebraic_empty
  compl_mem S hS := by
    rw [Set.mem_ofPred_eq, isMultiprojectiveSemialgebraic_def, piConePreimage_compl]
    exact isSemialgebraic_piConeDomain.sdiff hS
  union_mem _ _ hS hT := hS.union hT

@[simp]
theorem isMultiprojectiveSemialgebraic_univ :
    IsMultiprojectiveSemialgebraic (univ : Set ((i : ι) → ℙ K (κ i → K))) :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.univ_mem

theorem IsMultiprojectiveSemialgebraic.compl {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) : IsMultiprojectiveSemialgebraic Sᶜ :=
  isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.compl_mem hS

@[simp]
theorem isMultiprojectiveSemialgebraic_compl_iff {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraic Sᶜ ↔ IsMultiprojectiveSemialgebraic S :=
  ⟨fun h ↦ compl_compl S ▸ h.compl, IsMultiprojectiveSemialgebraic.compl⟩

theorem IsMultiprojectiveSemialgebraic.biInter {α : Type*} {t : Set α} (ht : t.Finite)
    {S : α → Set ((i : ι) → ℙ K (κ i → K))}
    (hS : ∀ a ∈ t, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋂ a ∈ t, S a) := by
  simpa using isSetAlgebra_setOf_isMultiprojectiveSemialgebraic.biInter_mem ht.toFinset
    (by simpa using hS)

theorem IsMultiprojectiveSemialgebraic.iInter {α : Type*} [Finite α]
    {S : α → Set ((i : ι) → ℙ K (κ i → K))} (hS : ∀ a, IsMultiprojectiveSemialgebraic (S a)) :
    IsMultiprojectiveSemialgebraic (⋂ a, S a) := by
  simpa using IsMultiprojectiveSemialgebraic.biInter finite_univ fun a _ ↦ hS a

end Finite

/-! ### Products, diagonals, and singletons of multiprojective spaces -/

/-- The product of two multiprojective semialgebraic sets is multiprojective semialgebraic. -/
theorem IsMultiprojectiveSemialgebraic.preimage_sumPiEquivProdPi_prod {ι' : Type*}
    {κ' : ι' → Type v}
    {S : Set ((i : ι) → ℙ K (κ i → K))} {T : Set ((j : ι') → ℙ K (κ' j → K))}
    (hS : IsMultiprojectiveSemialgebraic S) (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ' k → K)) ⁻¹' (S ×ˢ T)) := by
  rw [isMultiprojectiveSemialgebraic_def]
  convert (IsSemialgebraic.preimage_sumArrowEquivProdArrow_prod hS hT).preimage_comp
    (Equiv.sumSigmaDistrib (Sum.elim κ κ')).symm using 1
  ext w
  have hl (i : ι) :
      (fun j ↦ (Equiv.sumArrowEquivProdArrow ((i : ι) × κ i) ((j : ι') × κ' j) K
        (w ∘ (Equiv.sumSigmaDistrib (Sum.elim κ κ')).symm)).1 ⟨i, j⟩) =
        fun j ↦ w ⟨.inl i, j⟩ := funext fun j ↦ by
    rw [Equiv.sumArrowEquivProdArrow_apply_fst]
    exact congrArg w (Equiv.sumSigmaDistrib_symm_apply (Sum.elim κ κ') (.inl ⟨i, j⟩))
  have hr (j : ι') :
      (fun k ↦ (Equiv.sumArrowEquivProdArrow ((i : ι) × κ i) ((j : ι') × κ' j) K
        (w ∘ (Equiv.sumSigmaDistrib (Sum.elim κ κ')).symm)).2 ⟨j, k⟩) =
        fun k ↦ w ⟨.inr j, k⟩ := funext fun k ↦ by
    rw [Equiv.sumArrowEquivProdArrow_apply_snd]
    exact congrArg w (Equiv.sumSigmaDistrib_symm_apply (Sum.elim κ κ') (.inr ⟨j, k⟩))
  rw [mem_piConePreimage_iff, mem_preimage, mem_preimage, mem_prod,
    mem_piConePreimage_iff, mem_piConePreimage_iff]
  constructor
  · rintro ⟨hw, hmem⟩
    have hmem' := mem_prod.1 (mem_preimage.1 hmem)
    simp only [Equiv.sumPiEquivProdPi_apply] at hmem'
    exact ⟨⟨fun i ↦ (hl i).symm ▸ hw (.inl i), hmem'.1⟩,
      ⟨fun j ↦ (hr j).symm ▸ hw (.inr j), hmem'.2⟩⟩
  · rintro ⟨⟨h1, hSw⟩, ⟨h2, hTw⟩⟩
    refine ⟨Sum.rec (fun i ↦ hl i ▸ h1 i) (fun j ↦ hr j ▸ h2 j), mem_preimage.2 (mem_prod.2 ?_)⟩
    simp only [Equiv.sumPiEquivProdPi_apply]
    exact ⟨hSw, hTw⟩

/-- For finite `ι` and finite blocks `κ i`, the diagonal of `(i : ι) → ℙ K (κ i → K)` is
multiprojective semialgebraic: inside the punctured cone it is cut out by the `2 × 2` homogeneous
minor equations in each factor. -/
theorem isMultiprojectiveSemialgebraic_preimage_sumPiEquivProdPi_diagonal [Finite ι]
    [hκ : ∀ i, Finite (κ i)] :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ k → K)) ⁻¹'
        diagonal ((i : ι) → ℙ K (κ i → K))) := by
  have : ∀ k, Finite (Sum.elim κ κ k) := Sum.rec hκ hκ
  rw [isMultiprojectiveSemialgebraic_def]
  let minorPoly (i : ι) (a b : κ i) : MvPolynomial (Σ k : ι ⊕ ι, Sum.elim κ κ k) K :=
    X ⟨.inl i, a⟩ * X ⟨.inr i, b⟩
  convert isSemialgebraic_piConeDomain.inter <|
    IsSemialgebraic.iInter fun i ↦ IsSemialgebraic.iInter fun a ↦
      IsSemialgebraic.iInter fun b ↦
        isSemialgebraic_eval_eq (minorPoly i a b) (minorPoly i b a) using 1
  ext w
  rw [mem_piConePreimage_iff, mem_inter_iff, mem_piConeDomain_iff]
  refine ⟨fun ⟨hw, heq⟩ ↦ ⟨hw, mem_iInter.2 fun i ↦ mem_iInter.2 fun a ↦
      mem_iInter.2 fun b ↦ ?_⟩, fun ⟨hw, hmin⟩ ↦ ⟨hw, ?_⟩⟩
  · have hdiag : (fun i ↦ mk K (fun j ↦ w ⟨.inl i, j⟩) (hw (.inl i))) =
        fun i ↦ mk K (fun j ↦ w ⟨.inr i, j⟩) (hw (.inr i)) := by
      simpa only [Equiv.sumPiEquivProdPi_apply] using mem_diagonal_iff.1 (mem_preimage.1 heq)
    simpa only [Set.mem_ofPred_eq, minorPoly, map_mul, eval_X] using
      (mk_eq_mk_iff_forall_mul_eq (hw (.inl i)) (hw (.inr i))).1 (congr_fun hdiag i) a b
  · refine mem_preimage.2 (mem_diagonal_iff.2 ?_)
    simp only [Equiv.sumPiEquivProdPi_apply]
    refine funext fun i ↦
      (mk_eq_mk_iff_forall_mul_eq (hw (.inl i)) (hw (.inr i))).2 fun a b ↦ ?_
    simpa only [Set.mem_ofPred_eq, minorPoly, map_mul, eval_X] using
      mem_iInter.1 (mem_iInter.1 (mem_iInter.1 hmin i) a) b

/-- For finite `ι` and finite blocks `κ i`, every singleton in `(i : ι) → ℙ K (κ i → K)` is
multiprojective semialgebraic. -/
@[simp]
theorem isMultiprojectiveSemialgebraic_singleton [Finite ι] [∀ i, Finite (κ i)]
    (p : (i : ι) → ℙ K (κ i → K)) :
    IsMultiprojectiveSemialgebraic ({p} : Set ((i : ι) → ℙ K (κ i → K))) := by
  rw [isMultiprojectiveSemialgebraic_def]
  let f : (Σ k : ι ⊕ ι, Sum.elim κ κ k) → MvPolynomial (Σ i, κ i) K
    | ⟨.inl i, j⟩ => X ⟨i, j⟩
    | ⟨.inr i, j⟩ => C ((p i).rep j)
  convert isMultiprojectiveSemialgebraic_preimage_sumPiEquivProdPi_diagonal.preimage_eval f using 1
  ext v
  rw [mem_piConePreimage_iff, mem_preimage, mem_piConePreimage_iff]
  have h1 (i : ι) : (fun j ↦ eval v (f ⟨.inl i, j⟩)) = fun j ↦ v ⟨i, j⟩ :=
    funext fun j ↦ by simp [f]
  have h2 (i : ι) : (fun j ↦ eval v (f ⟨.inr i, j⟩)) = (p i).rep := funext fun j ↦ by simp [f]
  constructor
  · rintro ⟨hv, hvp⟩
    rw [mem_singleton_iff] at hvp
    refine ⟨Sum.rec (fun i ↦ (h1 i).symm ▸ hv i) (fun i ↦ (h2 i).symm ▸ (p i).rep_ne_zero),
      mem_preimage.2 (mem_diagonal_iff.2 ?_)⟩
    simp only [Equiv.sumPiEquivProdPi_apply]
    exact funext fun i ↦ by
      simp only [h1, h2]; exact (congr_fun hvp i).trans (p i).mk_rep.symm
  · rintro ⟨hv, hvp⟩
    have hdiag : (fun i ↦ mk K (fun j ↦ eval v (f ⟨.inl i, j⟩)) (hv (.inl i))) =
        fun i ↦ mk K (fun j ↦ eval v (f ⟨.inr i, j⟩)) (hv (.inr i)) := by
      simpa only [Equiv.sumPiEquivProdPi_apply] using mem_diagonal_iff.1 (mem_preimage.1 hvp)
    refine ⟨fun i ↦ h1 i ▸ hv (.inl i), mem_singleton_iff.2 (funext fun i ↦ ?_)⟩
    have hi := congr_fun hdiag i
    simp only [h1, h2] at hi
    exact hi.trans (p i).mk_rep

end MultiprojectiveSemialgebraic

/-! ### The product projector locus and embedded semialgebraicity -/

section ProductProjector

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {K : Type*} [Field K] [LinearOrder K]

omit [∀ i, Fintype (κ i)] in
private theorem isSemialgebraic_image_piMatrixLinearEquiv_univ_pi [Finite ι]
    (S : ∀ i, Set (Matrix (κ i) (κ i) K))
    (hS : ∀ i, IsSemialgebraic {b : κ i × κ i → K | Matrix.of (Function.curry b) ∈ S i}) :
    IsSemialgebraic (piMatrixLinearEquiv K κ κ K '' univ.pi S) := by
  rw [(piMatrixLinearEquiv K κ κ K).image_eq_preimage_symm]
  convert IsSemialgebraic.iInter fun i ↦
    (hS i).preimage_comp (Sigma.mk (β := fun i ↦ κ i × κ i) i) using 1
  ext a
  have hmat (i : ι) : (piMatrixLinearEquiv K κ κ K).symm a i =
      Matrix.of (Function.curry (a ∘ Sigma.mk (β := fun i ↦ κ i × κ i) i)) := by
    ext j k; simp [Function.curry]
  simp only [mem_preimage, mem_univ_pi, mem_iInter, mem_ofPred_eq, hmat]

/-- For finite `ι`, the flattened product projector locus is semialgebraic in
`(Σ i, κ i × κ i) → K`. -/
theorem isSemialgebraic_piProjectorLocus [Finite ι] :
    IsSemialgebraic (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) := by
  rw [piProjectorLocus_def]
  exact isSemialgebraic_image_piMatrixLinearEquiv_univ_pi _ fun _ ↦ isSemialgebraic_projectorLocus

/-- For finite `ι`, the factorwise rank-one projector map from `(Σ i, κ i) → K` into flattened
matrix entries `(Σ i, κ i × κ i) → K` is a semialgebraic map (with Lean's total division on
zero-norm blocks). -/
theorem isSemialgebraicMap_rankOneProjector [Finite ι] :
    IsSemialgebraicMap
      (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
        rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2) := by
  convert isSemialgebraicMap_eval_div
    (fun q : Σ i, κ i × κ i ↦ (X ⟨q.1, q.2.1⟩ * X ⟨q.1, q.2.2⟩ : MvPolynomial (Σ i, κ i) K))
    (fun q : Σ i, κ i × κ i ↦ ∑ r : κ q.1, X ⟨q.1, r⟩ * X ⟨q.1, r⟩) using 1
  ext v ⟨i, a, b⟩
  simp [rankOneProjector_apply, dotProduct]

/-- For finite `ι`, on the flattened punctured cone `piConeDomain κ K`, the factorwise rank-one
projector map into flattened matrix entries is semialgebraic. -/
theorem isSemialgebraicOn_rankOneProjector_piConeDomain [Finite ι] :
    IsSemialgebraicOn
      (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
        rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2)
      (piConeDomain κ K) :=
  isSemialgebraicMap_rankOneProjector.isSemialgebraicOn isSemialgebraic_piConeDomain

private theorem eq_empty_of_infinite_of_rightInvOn [Infinite ι]
    {τ : ((Σ i, κ i × κ i) → K) → ((i : ι) → ℙ K (κ i → K))}
    {s : Set ((Σ i, κ i × κ i) → K)} (hs : IsSemialgebraic s)
    (hτ : ∀ x ∈ s, piProjectorCoords (τ x) = x) : s = ∅ := by
  classical
  obtain ⟨F, hF⟩ := hs.exists_finset_mem_iff_of_eqOn
  obtain ⟨i₀, hi₀⟩ := Infinite.exists_notMem_finset (F.image Sigma.fst)
  have hnotMem (a b : κ i₀) : (⟨i₀, a, b⟩ : Σ i, κ i × κ i) ∉ F :=
    fun h ↦ hi₀ (Finset.mem_image.2 ⟨⟨i₀, a, b⟩, h, rfl⟩)
  refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  obtain ⟨a₀, _⟩ := Function.ne_iff.1 (τ x i₀).rep_ne_zero
  by_cases hsub : ∃ b₀ : κ i₀, b₀ ≠ a₀
  · obtain ⟨b₀, hb₀⟩ := hsub
    let y := Function.update (Function.update x ⟨i₀, a₀, b₀⟩ 1) ⟨i₀, b₀, a₀⟩ 0
    have hy : y ∈ s := (hF x y fun q hq ↦ by
      simp [y, show q ≠ ⟨i₀, b₀, a₀⟩ from fun h ↦ hnotMem b₀ a₀ (h ▸ hq),
        show q ≠ ⟨i₀, a₀, b₀⟩ from fun h ↦ hnotMem a₀ b₀ (h ▸ hq)]).1 hx
    have hsymm : projector (τ y i₀) a₀ b₀ = projector (τ y i₀) b₀ a₀ := by
      induction (τ y i₀) using ind with
      | h w hw => rw [projector_mk, rankOneProjector_apply, rankOneProjector_apply, mul_comm]
    have hya : projector (τ y i₀) a₀ b₀ = 1 := by
      simpa [y, show (⟨i₀, a₀, b₀⟩ : Σ i, κ i × κ i) ≠ ⟨i₀, b₀, a₀⟩ by simp [hb₀.symm]] using
        congr_fun (hτ y hy) ⟨i₀, a₀, b₀⟩
    have hyb : projector (τ y i₀) b₀ a₀ = 0 := by simpa [y] using congr_fun (hτ y hy) ⟨i₀, b₀, a₀⟩
    exact one_ne_zero (hya.symm.trans (hsymm.trans hyb))
  · push Not at hsub
    have : Subsingleton (κ i₀) := ⟨fun a b ↦ (hsub a).trans (hsub b).symm⟩
    let y := Function.update x ⟨i₀, a₀, a₀⟩ 0
    have hy : y ∈ s := (hF x y fun q hq ↦ by
      simp [y, show q ≠ ⟨i₀, a₀, a₀⟩ from fun h ↦ hnotMem a₀ a₀ (h ▸ hq)]).1 hx
    have hy0 : projector (τ y i₀) a₀ a₀ = 0 := by simpa [y] using congr_fun (hτ y hy) ⟨i₀, a₀, a₀⟩
    exact one_ne_zero ((projector_apply_eq_one (τ y i₀) a₀ a₀).symm.trans hy0)

omit [∀ i, Fintype (κ i)] in
private theorem eq_empty_of_infinite_of_isMultiprojectiveSemialgebraic [Infinite ι]
    {S : Set ((i : ι) → ℙ K (κ i → K))} (hS : IsMultiprojectiveSemialgebraic S) : S = ∅ := by
  classical
  obtain ⟨F, hF⟩ := hS.exists_finset_mem_iff_of_eqOn
  obtain ⟨i₀, hi₀⟩ := Infinite.exists_notMem_finset (F.image Sigma.fst)
  refine eq_empty_iff_forall_notMem.2 fun p hpS ↦ ?_
  let v : (Σ i, κ i) → K := fun q ↦ (p q.1).rep q.2
  have hvS : v ∈ piConePreimage S := mem_piConePreimage_iff.2 ⟨fun i ↦ (p i).rep_ne_zero, by
    convert hpS using 1; exact funext fun i ↦ (p i).mk_rep⟩
  let w : (Σ i, κ i) → K := fun q ↦ if q.1 = i₀ then 0 else v q
  have hwS : w ∈ piConePreimage S := (hF v w fun q hq ↦ by
    simp [w, show q.1 ≠ i₀ from fun h ↦ hi₀ (Finset.mem_image.2 ⟨q, hq, h⟩)]).1 hvS
  exact (mem_piConePreimage_iff.1 hwS).1 i₀ (funext fun j ↦ by simp [w])

/-- **Inverse projector transport on semialgebraic subsets of the flattened product projector
locus.** Any map `τ : ((Σ i, κ i × κ i) → K) → (i : ι) → ℙ K (κ i → K)` that is a right inverse of
`piProjectorCoords` on a semialgebraic set `s` satisfies
`IsSemialgebraicOn (piProjectorCoords ∘ τ) s`. Over an ordered field with
`[IsStrictOrderedRing K]` and `[HasSemialgebraicProjections K]`, this combines with
`IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image` (for finite `ι` and
`[Finite (Σ i, κ i × κ i)]`) and
`IsSemialgebraicOn.isSemialgebraic_inter_preimage_of_isMultiprojectiveSemialgebraic` to push
semialgebraic subsets of `s` forward and pull multiprojective semialgebraic sets back. -/
theorem isSemialgebraicOn_piProjectorCoords_comp_of_rightInvOn
    {τ : ((Σ i, κ i × κ i) → K) → ((i : ι) → ℙ K (κ i → K))}
    {s : Set ((Σ i, κ i × κ i) → K)} (hs : IsSemialgebraic s)
    (hτ : ∀ x ∈ s, piProjectorCoords (τ x) = x) :
    IsSemialgebraicOn (piProjectorCoords ∘ τ) s := by
  by_cases hι : Finite ι
  · exact (isSemialgebraicMap_id.isSemialgebraicOn hs).congr fun x hx ↦ (hτ x hx).symm
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    rw [eq_empty_of_infinite_of_rightInvOn hs hτ]
    exact isSemialgebraicOn_empty _

variable [IsStrictOrderedRing K]

/-- **Complement transport in flattened matrix coordinates.** For finite `ι`, the embedded image of
`Sᶜ` under `piProjectorCoords` is semialgebraic if and only if `piProjectorCoords '' S` is, since
the two are relative complements inside the semialgebraic flattened product projector locus. -/
@[simp]
theorem isSemialgebraic_image_piProjectorCoords_compl_iff [Finite ι]
    {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsSemialgebraic (piProjectorCoords '' Sᶜ) ↔ IsSemialgebraic (piProjectorCoords '' S) :=
  ⟨fun h ↦ by
      rw [← compl_compl S, image_piProjectorCoords_compl]
      exact isSemialgebraic_piProjectorLocus.sdiff h,
    fun h ↦ image_piProjectorCoords_compl S ▸ isSemialgebraic_piProjectorLocus.sdiff h⟩

/-- For finite `ι`, the image of a standard product affine open `piAffineOpen I` under
`piProjectorCoords` is semialgebraic. -/
theorem isSemialgebraic_image_piProjectorCoords_piAffineOpen [Finite ι] (I : ∀ i, κ i) :
    IsSemialgebraic (piProjectorCoords '' piAffineOpen (K := K) I) := by
  rw [piProjectorCoords_def, image_comp, piProjector_def, piAffineOpen_def, Set.piMap_image_univ_pi]
  exact isSemialgebraic_image_piMatrixLinearEquiv_univ_pi _ fun i ↦
    isSemialgebraic_image_projector_affineOpen (I i)

private theorem image_piProjectorCoords_eq_inter_iUnion (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piProjectorCoords '' S =
      (piMatrixLinearEquiv K κ κ K '' piProjectorLocus κ K) ∩
        ⋃ R : ∀ i, κ i,
          (⋂ i : ι, {a | eval a (X ⟨i, R i, R i⟩ : MvPolynomial (Σ i, κ i × κ i) K) ≠ 0}) ∩
            (fun a : (Σ i, κ i × κ i) → K ↦ a ∘ fun q : Σ i, κ i ↦ ⟨q.1, R q.1, q.2⟩) ⁻¹'
              piConePreimage S := by
  ext a
  constructor
  · rintro ⟨p, hpS, rfl⟩
    obtain ⟨R, hpR⟩ := exists_mem_piAffineOpen p
    have hR (i : ι) : projector (p i) (R i) (R i) ≠ 0 :=
      (projector_apply_self_pos_iff.2 (mem_piAffineOpen_iff.1 hpR i)).ne'
    have hv (i : ι) : (fun j ↦ piProjectorCoords p ⟨i, R i, j⟩) ≠ 0 :=
      fun h0 ↦ hR i (by simpa using congr_fun h0 (R i))
    refine ⟨(range_piProjectorCoords (κ := κ) (K := K)) ▸ mem_range_self p,
      mem_iUnion.2 ⟨R, mem_iInter.2 fun i ↦ by simpa using hR i,
        mem_piConePreimage_iff.2 ⟨hv, ?_⟩⟩⟩
    convert hpS using 1
    exact funext fun i ↦ mk_piProjectorCoords_row_eq p (hR i) (hv i)
  · rintro ⟨haL, haU⟩
    obtain ⟨p, rfl⟩ := (range_piProjectorCoords (κ := κ) (K := K)).symm ▸ haL
    obtain ⟨R, hdiag, hpre⟩ := mem_iUnion.1 haU
    obtain ⟨hv, hpS⟩ := mem_piConePreimage_iff.1 hpre
    have hR (i : ι) : projector (p i) (R i) (R i) ≠ 0 := by
      simpa using mem_iInter.1 hdiag i
    refine ⟨p, ?_, rfl⟩
    convert hpS using 1
    exact (funext fun i ↦ mk_piProjectorCoords_row_eq p (hR i) (hv i)).symm

private theorem inter_preimage_rankOneProjector_piProjectorCoords
    (S : Set ((i : ι) → ℙ K (κ i → K))) :
    piConeDomain κ K ∩
        (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
          rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2) ⁻¹' (piProjectorCoords '' S) =
      piConePreimage S := by
  ext v
  rw [mem_inter_iff, mem_piConeDomain_iff, mem_piConePreimage_iff]
  constructor
  · rintro ⟨hv, q, hqS, hq⟩
    refine ⟨hv, ?_⟩
    have heq : piProjectorCoords (fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i)) =
        piProjectorCoords q := by
      ext ⟨i, j, k⟩
      simpa using (congr_fun hq ⟨i, j, k⟩).symm
    rwa [piProjectorCoords_injective heq]
  · rintro ⟨hv, hp⟩
    refine ⟨hv, fun i ↦ mk K (fun j ↦ v ⟨i, j⟩) (hv i), hp, ?_⟩
    ext ⟨i, j, k⟩
    simp

/-- **Equivalence of cone and embedded-projector semialgebraicity.** Over any ordered field, a
subset `S` of a multiprojective space `(i : ι) → ℙ K (κ i → K)` (with finite blocks `κ i`) is
multiprojective semialgebraic if and only if its image `piProjectorCoords '' S` in the flattened
matrix space `(Σ i, κ i × κ i) → K` is semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords
    {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraic S ↔ IsSemialgebraic (piProjectorCoords '' S) := by
  by_cases hι : Finite ι
  · constructor
    · intro hS
      rw [image_piProjectorCoords_eq_inter_iUnion]
      exact (isSemialgebraic_piProjectorLocus (κ := κ) (K := K)).inter <|
        IsSemialgebraic.iUnion fun R ↦
          (IsSemialgebraic.iInter fun i ↦
            isSemialgebraic_eval_ne_zero
              (X ⟨i, R i, R i⟩ : MvPolynomial (Σ i, κ i × κ i) K)).inter
            (hS.preimage_comp fun q ↦ (⟨q.1, R q.1, q.2⟩ : Σ i, κ i × κ i))
    · intro himg
      rw [isMultiprojectiveSemialgebraic_def, ← inter_preimage_rankOneProjector_piProjectorCoords]
      let N (q : Σ i, κ i × κ i) : MvPolynomial (Σ i, κ i) K :=
        X ⟨q.1, q.2.1⟩ * X ⟨q.1, q.2.2⟩
      let D (q : Σ i, κ i × κ i) : MvPolynomial (Σ i, κ i) K :=
        ∑ r : κ q.1, X ⟨q.1, r⟩ * X ⟨q.1, r⟩
      have hfun : (fun (v : (Σ i, κ i) → K) (q : Σ i, κ i × κ i) ↦
          rankOneProjector (fun j ↦ v ⟨q.1, j⟩) q.2.1 q.2.2) =
          fun v q ↦ eval v (N q) / eval v (D q) := by
        ext v q
        simp [N, D, rankOneProjector_apply, dotProduct]
      rw [hfun]
      exact isSemialgebraic_piConeDomain.inter (himg.preimage_eval_div N D)
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    constructor
    · intro hS
      rw [eq_empty_of_infinite_of_isMultiprojectiveSemialgebraic hS, image_empty]
      exact isSemialgebraic_empty
    · intro himg
      by_cases hne : S.Nonempty
      · obtain ⟨p₀, _⟩ := hne
        classical
        let τ (a : (Σ i, κ i × κ i) → K) : (i : ι) → ℙ K (κ i → K) :=
          if h : a ∈ piProjectorCoords '' S then h.choose else p₀
        have hτ : ∀ a ∈ piProjectorCoords '' S, piProjectorCoords (τ a) = a := by
          intro a ha
          simp only [τ, dite_eq_left ha]
          exact ha.choose_spec.2
        have hS0 : S = ∅ := image_eq_empty.1 (eq_empty_of_infinite_of_rightInvOn himg hτ)
        rw [hS0]
        exact isMultiprojectiveSemialgebraic_empty
      · rw [not_nonempty_iff_eq_empty.1 hne]
        exact isMultiprojectiveSemialgebraic_empty

/-- Over an ordered field with semialgebraic projections (`HasSemialgebraicProjections K`), if
`piProjectorCoords ∘ f` is semialgebraic on a finite-coordinate affine set `s`, then `f '' s` is
multiprojective semialgebraic. -/
theorem IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image {σ : Type*}
    [HasSemialgebraicProjections K] [Finite σ]
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)}
    (hf : IsSemialgebraicOn (piProjectorCoords ∘ f) s) :
    IsMultiprojectiveSemialgebraic (f '' s) := by
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords, ← image_comp]
  exact hf.isSemialgebraic_image

/-- Over an ordered field with semialgebraic projections (`HasSemialgebraicProjections K`), if
`piProjectorCoords ∘ f` is semialgebraic on `s`, then the preimage in `s` of every multiprojective
semialgebraic subset `T` is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_preimage_of_isMultiprojectiveSemialgebraic
    {σ : Type*} [HasSemialgebraicProjections K]
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)}
    (hf : IsSemialgebraicOn (piProjectorCoords ∘ f) s)
    {T : Set ((i : ι) → ℙ K (κ i → K))} (hT : IsMultiprojectiveSemialgebraic T) :
    IsSemialgebraic (s ∩ f ⁻¹' T) := by
  by_cases hι : Finite ι
  · have hT' := isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords.1 hT
    have hpre : s ∩ f ⁻¹' T = s ∩ (piProjectorCoords ∘ f) ⁻¹' (piProjectorCoords '' T) := by
      ext x
      simp [piProjectorCoords_injective.mem_set_image]
    rw [hpre]
    exact hf.isSemialgebraic_inter_preimage hT'
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    rw [eq_empty_of_infinite_of_isMultiprojectiveSemialgebraic hT]
    simp

end ProductProjector

/-! ### Standard product affine charts and local-to-global semialgebraicity -/

section ProductAffineCharts

variable {ι : Type*} {n : ι → ℕ} {K : Type*} [Field K]

private noncomputable def piAffineChartLiftPoly (I : ∀ i, Fin (n i + 1)) :
    (Σ i, Fin (n i + 1)) → MvPolynomial (Σ i, Fin (n i)) K := fun ⟨i, j⟩ ↦
  Fin.insertNth (α := fun _ ↦ MvPolynomial (Σ i, Fin (n i)) K) (I i) 1 (fun k ↦ X ⟨i, k⟩) j

private theorem eval_piAffineChartLiftPoly (I : ∀ i, Fin (n i + 1))
    (z : (Σ i, Fin (n i)) → K) (i : ι) (j : Fin (n i + 1)) :
    eval z (piAffineChartLiftPoly I ⟨i, j⟩) =
      Fin.insertNth (α := fun _ ↦ K) (I i) 1 (fun k ↦ z ⟨i, k⟩) j := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove (I i) j <;>
    simp [piAffineChartLiftPoly]

variable [LinearOrder K]

/-- Every multiprojective semialgebraic set is semialgebraic in every standard product affine chart
(requiring neither finiteness of `ι` nor projection closure). -/
theorem IsMultiprojectiveSemialgebraic.isSemialgebraic_image_piAffineChart
    {S : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} (hS : IsMultiprojectiveSemialgebraic S)
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraic (piAffineChart I '' (S ∩ piAffineOpen I)) := by
  have hv (z : (Σ i, Fin (n i)) → K) (i : ι) :
      (fun j ↦ eval z (piAffineChartLiftPoly I ⟨i, j⟩)) ≠ 0 := by
    simpa only [funext (eval_piAffineChartLiftPoly I z i)] using
      Fin.insertNth_one_ne_zero (I i) fun k ↦ z ⟨i, k⟩
  have hmk (z : (Σ i, Fin (n i)) → K)
      (hvz : ∀ i, (fun j ↦ eval z (piAffineChartLiftPoly I ⟨i, j⟩)) ≠ 0) :
      (fun i ↦ mk K (fun j ↦ eval z (piAffineChartLiftPoly I ⟨i, j⟩)) (hvz i)) =
        (piAffineChart I).symm z := by
    ext i
    simp [funext (eval_piAffineChartLiftPoly I z i)]
  convert IsSemialgebraic.preimage_eval hS (piAffineChartLiftPoly I) using 1
  ext z
  rw [mem_preimage, mem_piConePreimage_iff]
  constructor
  · rintro ⟨p, ⟨hpS, hpI⟩, rfl⟩
    refine ⟨hv _, ?_⟩
    rw [hmk, (piAffineChart I).left_inv (by simpa using hpI)]
    exact hpS
  · rintro ⟨hvz, hpS⟩
    rw [hmk] at hpS
    exact ⟨(piAffineChart I).symm z, ⟨hpS, by simp⟩, (piAffineChart I).right_inv (by simp)⟩

/-- For finite `ι`, the inverse of a standard product affine chart followed by `piProjectorCoords`
is a semialgebraic map. -/
theorem isSemialgebraicMap_piProjectorCoords_piAffineChart_symm [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicMap
      (piProjectorCoords ∘ (piAffineChart (K := K) I).symm) := by
  rw [← isSemialgebraicOn_univ]
  refine (isSemialgebraicOn_univ.2
    (isSemialgebraicMap_rankOneProjector.comp_eval
      (piAffineChartLiftPoly (K := K) I))).congr fun z _ ↦ ?_
  ext ⟨i, a, b⟩
  simp only [Function.comp_apply, piProjectorCoords_apply, piAffineChart_symm_apply,
    affineChart_symm_apply, projector_mk]
  simp only [funext (eval_piAffineChartLiftPoly I z i)]

variable [IsStrictOrderedRing K]

/-- For finite `ι`, the standard product affine chart `piAffineChart I` read in the flattened
product projector model is semialgebraic on `piProjectorCoords '' piAffineOpen I`. -/
theorem isSemialgebraicOn_piProjectorCoords_piAffineChart [Finite ι]
    (I : ∀ i, Fin (n i + 1)) :
    IsSemialgebraicOn
      (fun (a : (Σ i, Fin (n i + 1) × Fin (n i + 1)) → K) (q : Σ i, Fin (n i)) ↦
        a ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ / a ⟨q.1, I q.1, I q.1⟩)
      (piProjectorCoords '' piAffineOpen (K := K) I) := by
  simpa using isSemialgebraicOn_eval_div
    (fun q : Σ i, Fin (n i) ↦
      (X ⟨q.1, (I q.1).succAbove q.2, I q.1⟩ :
        MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K))
    (fun q : Σ i, Fin (n i) ↦ X ⟨q.1, I q.1, I q.1⟩)
    (isSemialgebraic_image_piProjectorCoords_piAffineOpen I)

/-- For finite `ι`, if the chart image of `S ∩ piAffineOpen I` is semialgebraic, then
`piProjectorCoords '' (S ∩ piAffineOpen I)` is semialgebraic (without needing projection
closure). -/
theorem isSemialgebraic_image_piProjectorCoords_inter_piAffineOpen [Finite ι]
    {S : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    (hSI : IsSemialgebraic (piAffineChart I '' (S ∩ piAffineOpen I))) :
    IsSemialgebraic (piProjectorCoords '' (S ∩ piAffineOpen I)) := by
  let N (q : Σ i, Fin (n i)) : MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K :=
    X ⟨q.1, (I q.1).succAbove q.2, I q.1⟩
  let D (q : Σ i, Fin (n i)) : MvPolynomial (Σ i, Fin (n i + 1) × Fin (n i + 1)) K :=
    X ⟨q.1, I q.1, I q.1⟩
  have hdiv (p) : (fun q ↦ eval (piProjectorCoords p) (N q) / eval (piProjectorCoords p) (D q)) =
      piAffineChart I p := by
    simpa [N, D] using (piAffineChart_eq_piProjectorCoords_div I p).symm
  convert (isSemialgebraic_image_piProjectorCoords_piAffineOpen I).inter
    (hSI.preimage_eval_div N D) using 1
  ext a
  constructor
  · rintro ⟨p, ⟨hpS, hpI⟩, rfl⟩
    exact ⟨⟨p, hpI, rfl⟩, mem_preimage.2 (hdiv p ▸ ⟨p, ⟨hpS, hpI⟩, rfl⟩)⟩
  · rintro ⟨⟨p, hpI, rfl⟩, hmem⟩
    obtain ⟨q, ⟨hqS, hqI⟩, hqp⟩ := hdiv p ▸ mem_preimage.1 hmem
    have hpq : q = p := (piAffineChart I).injOn (by simpa using hqI) (by simpa using hpI) hqp
    exact ⟨p, ⟨hpq ▸ hqS, hpI⟩, rfl⟩

/-- **Single-chart inverse transport.** Over any ordered field and for finite `ι`, the image of an
affine subset `s` under the inverse standard product affine chart `(piAffineChart I).symm` is
multiprojective semialgebraic if and only if `s` is semialgebraic (without needing projection
closure). -/
theorem isMultiprojectiveSemialgebraic_image_piAffineChart_symm_iff [Finite ι]
    (I : ∀ i, Fin (n i + 1)) {s : Set ((Σ i, Fin (n i)) → K)} :
    IsMultiprojectiveSemialgebraic ((piAffineChart (K := K) I).symm '' s) ↔
      IsSemialgebraic s := by
  have hchart : piAffineChart I '' (((piAffineChart (K := K) I).symm '' s) ∩ piAffineOpen I) =
      s := by
    ext z
    refine ⟨?_, fun hz ↦ ⟨(piAffineChart I).symm z, ⟨⟨z, hz, rfl⟩, by simp⟩,
      (piAffineChart I).right_inv (by simp)⟩⟩
    rintro ⟨_, ⟨⟨w, hw, rfl⟩, _⟩, rfl⟩
    rwa [(piAffineChart I).right_inv (by simp)]
  refine ⟨fun h ↦ hchart ▸ h.isSemialgebraic_image_piAffineChart I, fun hs ↦ ?_⟩
  have hsub : (piAffineChart (K := K) I).symm '' s =
      ((piAffineChart (K := K) I).symm '' s) ∩ piAffineOpen I :=
    (inter_eq_left.2 (by rintro _ ⟨z, _, rfl⟩; simp)).symm
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords, hsub]
  exact isSemialgebraic_image_piProjectorCoords_inter_piAffineOpen (hchart.symm ▸ hs)

/-- **Single-chart preimage transport.** Over any ordered field and for finite `ι`,
`piAffineOpen I ∩ piAffineChart I ⁻¹' s` is multiprojective semialgebraic if and only if `s` is
semialgebraic (without needing projection closure). -/
theorem isMultiprojectiveSemialgebraic_piAffineOpen_inter_preimage_piAffineChart_iff [Finite ι]
    (I : ∀ i, Fin (n i + 1)) {s : Set ((Σ i, Fin (n i)) → K)} :
    IsMultiprojectiveSemialgebraic (piAffineOpen (K := K) I ∩ piAffineChart I ⁻¹' s) ↔
      IsSemialgebraic s := by
  have heq : piAffineOpen (K := K) I ∩ piAffineChart I ⁻¹' s =
      (piAffineChart (K := K) I).symm '' s := by
    ext p
    exact ⟨fun ⟨hpI, hps⟩ ↦
        ⟨piAffineChart I p, hps, (piAffineChart I).left_inv (by simpa using hpI)⟩,
      fun ⟨z, hzs, hp⟩ ↦
        hp ▸ ⟨by simp, by simpa [(piAffineChart I).right_inv (by simp)] using hzs⟩⟩
  rw [heq, isMultiprojectiveSemialgebraic_image_piAffineChart_symm_iff]

/-- **Chart characterization of multiprojective semialgebraic sets.** Over any ordered field, a
subset `S` of a finite multiprojective space `(i : ι) → ℙ K (Fin (n i + 1) → K)` is
multiprojective semialgebraic if and only if its image in every standard product affine chart is
semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_isSemialgebraic_image_piAffineChart [Finite ι]
    {S : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ I : ∀ i, Fin (n i + 1), IsSemialgebraic (piAffineChart I '' (S ∩ piAffineOpen I)) := by
  refine ⟨fun hS I ↦ hS.isSemialgebraic_image_piAffineChart I, fun hS ↦ ?_⟩
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords]
  convert IsSemialgebraic.iUnion
    (fun I ↦ isSemialgebraic_image_piProjectorCoords_inter_piAffineOpen (hS I)) using 1
  ext a
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨p, hpS, rfl⟩
    obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
    exact ⟨I, p, ⟨hpS, hpI⟩, rfl⟩
  · rintro ⟨I, p, ⟨hpS, _⟩, rfl⟩
    exact ⟨p, hpS, rfl⟩

end ProductAffineCharts

section RealProductAffineCharts

variable {ι : Type*} {n : ι → ℕ} [Finite ι]

/-- **Local-to-global semialgebraicity on real multiprojective space.** If at every point
`p ∈ closure S` of `M = (i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ)` there is a standard product affine chart
`I` containing `p` in which `S` is semialgebraic at `piAffineChart I p`, then `S` is globally
multiprojective semialgebraic. -/
theorem isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt
    {S : Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ))}
    (hS : ∀ p ∈ closure S, ∃ I : ∀ i, Fin (n i + 1), p ∈ piAffineOpen I ∧
      SemialgebraicAt (piAffineChart I '' (S ∩ piAffineOpen I)) (piAffineChart I p)) :
    IsMultiprojectiveSemialgebraic S := by
  cases nonempty_fintype ι
  choose I hpI hloc using hS
  choose ε hε hball using fun p hp ↦ (semialgebraicAt_iff_exists_ball.1 (hloc p hp))
  let W : ∀ p ∈ closure S, Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ)) :=
    fun p hp ↦ piAffineOpen (I p hp) ∩
      piAffineChart (I p hp) ⁻¹' Metric.ball (piAffineChart (I p hp) p) (ε p hp)
  have hWo (p) (hp : p ∈ closure S) : IsOpen (W p hp) :=
    (continuousOn_piAffineChart (I p hp)).isOpen_inter_preimage
      (isOpen_piAffineOpen (I p hp)) Metric.isOpen_ball
  have hpW (p) (hp : p ∈ closure S) : p ∈ W p hp := ⟨hpI p hp, Metric.mem_ball_self (hε p hp)⟩
  -- Compactness of `closure S` yields finitely many chart-ball neighborhoods covering `S`, and
  -- `piProjectorCoords ∘ (piAffineChart (I p hp)).symm` pushes the intersections of the chart
  -- images of `S` with those balls forward to cover `piProjectorCoords '' S`.
  obtain ⟨t, ht⟩ := isClosed_closure.isCompact.elim_nhds_subcover' W
    fun p hp ↦ (hWo p hp).mem_nhds (hpW p hp)
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords]
  convert IsSemialgebraic.biUnion t.finite_toSet fun p _ ↦
    (isSemialgebraicMap_piProjectorCoords_piAffineChart_symm
        (I p.val p.property)).isSemialgebraic_image
      (hball p.val p.property) using 1
  ext a
  simp only [mem_image, mem_iUnion, exists_prop, Function.comp_apply]
  constructor
  · rintro ⟨q, hqS, rfl⟩
    obtain ⟨p, hpt, hqW⟩ := mem_iUnion₂.1 (ht (subset_closure hqS))
    refine ⟨p, hpt, piAffineChart (I p.val p.property) q, ⟨⟨q, ⟨hqS, hqW.1⟩, rfl⟩, hqW.2⟩, ?_⟩
    rw [(piAffineChart (I p.val p.property)).left_inv (by simpa using hqW.1)]
  · rintro ⟨p, _, _, ⟨⟨q, ⟨hqS, hqI⟩, rfl⟩, _⟩, rfl⟩
    refine ⟨q, hqS, ?_⟩
    rw [(piAffineChart (I p.val p.property)).left_inv (by simpa using hqI)]

/-- Over `ℝ`, a subset of a finite multiprojective space is multiprojective semialgebraic if and
only if every ambient point admits a standard product affine chart in which the set is locally
semialgebraic at that point. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_exists_semialgebraicAt
    {S : Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p, ∃ I : ∀ i, Fin (n i + 1), p ∈ piAffineOpen I ∧
        SemialgebraicAt (piAffineChart I '' (S ∩ piAffineOpen I)) (piAffineChart I p) := by
  refine ⟨fun hS p ↦ ?_, fun hS ↦
    isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt fun p _ ↦ hS p⟩
  obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
  exact ⟨I, hpI, (hS.isSemialgebraic_image_piAffineChart I).semialgebraicAt _⟩

/-- Over `ℝ`, a subset of a finite multiprojective space is multiprojective semialgebraic if and
only if it is locally semialgebraic at every ambient point in every standard product affine chart
containing that point. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt
    {S : Set ((i : ι) → ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p (I : ∀ i, Fin (n i + 1)), p ∈ piAffineOpen I →
        SemialgebraicAt (piAffineChart I '' (S ∩ piAffineOpen I)) (piAffineChart I p) := by
  refine ⟨fun hS p I _ ↦ (hS.isSemialgebraic_image_piAffineChart I).semialgebraicAt _, fun hS ↦ ?_⟩
  refine isMultiprojectiveSemialgebraic_of_forall_exists_semialgebraicAt fun p _ ↦ ?_
  obtain ⟨I, hpI⟩ := exists_mem_piAffineOpen p
  exact ⟨I, hpI, hS p I hpI⟩

end RealProductAffineCharts

end TauCeti
