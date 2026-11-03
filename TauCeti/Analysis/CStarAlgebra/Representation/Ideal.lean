/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.Projection.ExtendByZero

/-!
# Degenerate multiplier extensions and extensions of representations from closed ideals

Let `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` be a (not necessarily nondegenerate) Hilbert-space representation
of a possibly nonunital C⋆-algebra `A`. Its *essential subspace* `π.essentialSubspace` is the
closed linear span of the ranges `Set.range (π a)`. Every operator `π a` maps `H` into
`π.essentialSubspace` and annihilates its orthogonal complement `π.essentialSubspaceᗮ`, so
compressing `π` to `π.essentialSubspace` yields a nondegenerate representation
`π.restrictEssentialSubspace : A →⋆ₙₐ[ℂ] (π.essentialSubspace →L[ℂ] π.essentialSubspace)` whose
extension by zero recovers `π`.

Extending `π.restrictEssentialSubspace` to `𝓜(ℂ, A)` via `NonUnitalStarAlgHom.multiplierExtension`
and composing with `π.essentialSubspace.extendByZero` produces a canonical nonunital star-algebra
homomorphism `π.nonUnitalMultiplierExtension : 𝓜(ℂ, A) →⋆ₙₐ[ℂ] (H →L[ℂ] H)` on the *same* Hilbert
space `H`, sending `1 : 𝓜(ℂ, A)` to `π.essentialSubspace.starProjection`, converging strongly along
any increasing approximate unit of `A`, and agreeing with `π.multiplierExtension hπ` whenever `π`
is nondegenerate.

Composing further with `I.multiplierHom hmul : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` extends any representation
`π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a closed two-sided star ideal `I` of `A` to a representation
`π.idealExtension hmul : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` on the same Hilbert space `H`, with the same
essential subspace. Keeping the ambient Hilbert space unchanged allows covariant representations of
C⋆-dynamical systems on closed invariant ideals to extend with the same unitary group
representation.

## Main definitions and results

* `NonUnitalStarAlgHom.essentialSubspace`: the closed span of all ranges `Set.range (π a)`, with
  `mem_orthogonal_essentialSubspace_iff` characterizing its orthogonal complement as the common
  kernel `⋂ a, ker (π a)`.
* `NonUnitalStarAlgHom.ext_of_orthogonal_essentialSubspace`: bounded operators agreeing after
  right multiplication by `π a` and on `π.essentialSubspaceᗮ` are equal on `H`.
* `NonUnitalStarAlgHom.restrictEssentialSubspace` and
  `NonUnitalStarAlgHom.isNondegenerate_restrictEssentialSubspace`: the nondegenerate compression of
  `π` to its essential subspace.
* `NonUnitalStarAlgHom.nonUnitalMultiplierExtension`: the canonical extension
  `𝓜(ℂ, A) →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a possibly degenerate representation, uniquely characterized
  by `eq_nonUnitalMultiplierExtension_iff`, sending `1` to `π.essentialSubspace.starProjection`,
  and agreeing with `π.multiplierExtension` when `π.IsNondegenerate`.
* `NonUnitalStarAlgHom.idealExtension`: extension of a representation `π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H)`
  of a closed two-sided star ideal `I` of `A` to `A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` on the same `H`, with
  `idealExtension_coe`, `eq_idealExtension_iff`, `essentialSubspace_idealExtension`, and
  `isNondegenerate_idealExtension_iff`.

## References

* Jacques Dixmier, *C*-Algebras*, Proposition 2.10.4.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.50 and Corollary 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Section 1.1 and Proposition 3.19.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra InnerProductSpace

namespace NonUnitalStarAlgHom

section EssentialSubspace

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The *essential subspace* of a Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`: the
closed linear span of all vectors `π a ξ`. -/
def essentialSubspace (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (Submodule.span ℂ (⋃ a, Set.range (π a))).topologicalClosure

/-- The essential subspace of a representation is closed. -/
theorem isClosed_essentialSubspace (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (π.essentialSubspace : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : CompleteSpace π.essentialSubspace :=
  π.isClosed_essentialSubspace.completeSpace_coe

variable {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

/-- Every vector in the range of `π a` belongs to `π.essentialSubspace`. -/
theorem apply_mem_essentialSubspace (a : A) (ξ : H) : π a ξ ∈ π.essentialSubspace :=
  Submodule.le_topologicalClosure _ <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨a, ξ, rfl⟩

/-- A closed submodule contains `π.essentialSubspace` if and only if it contains every vector
`π a ξ`. -/
theorem essentialSubspace_le_iff {K : Submodule ℂ H} (hK : IsClosed (K : Set H)) :
    π.essentialSubspace ≤ K ↔ ∀ a ξ, π a ξ ∈ K := by
  refine ⟨fun h a ξ => h (π.apply_mem_essentialSubspace a ξ), fun h => ?_⟩
  exact hK.closure_subset_iff.2 <| Submodule.span_le.2 <|
    Set.iUnion_subset fun a => Set.range_subset_iff.2 (h a)

/-- A vector lies in the orthogonal complement of `π.essentialSubspace` if and only if it is
annihilated by every operator `π a`. -/
theorem mem_orthogonal_essentialSubspace_iff {ξ : H} :
    ξ ∈ π.essentialSubspaceᗮ ↔ ∀ a, π a ξ = 0 := by
  refine ⟨fun hξ a => ext_inner_left ℂ fun v => ?_, fun hξ => ?_⟩
  · rw [inner_zero_right, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    exact (Submodule.mem_orthogonal _ _).1 hξ _ (π.apply_mem_essentialSubspace (star a) v)
  · rw [Submodule.mem_orthogonal']
    refine (innerSL ℂ ξ).isClosed_ker.closure_subset_iff.2 <|
      (Submodule.span_le (p := (innerSL ℂ ξ).ker)).2 fun y hy => ?_
    obtain ⟨a, v, rfl⟩ := Set.mem_iUnion.1 hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, hξ (star a), inner_zero_left]

/-- Every operator `π a` vanishes on `π.essentialSubspaceᗮ`. -/
theorem apply_eq_zero_of_mem_orthogonal_essentialSubspace {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) (a : A) : π a ξ = 0 :=
  π.mem_orthogonal_essentialSubspace_iff.1 hξ a

/-- A representation is nondegenerate if and only if its essential subspace is `⊤`. -/
theorem isNondegenerate_iff_essentialSubspace_eq_top :
    π.IsNondegenerate ↔ π.essentialSubspace = ⊤ :=
  π.isNondegenerate_iff_dense.trans Submodule.dense_iff_topologicalClosure_eq_top

/-- The orthogonal complement of the essential subspace of a nondegenerate representation is `⊥`. -/
theorem orthogonal_essentialSubspace_eq_bot_of_isNondegenerate (hπ : π.IsNondegenerate) :
    π.essentialSubspaceᗮ = ⊥ := by
  rw [π.isNondegenerate_iff_essentialSubspace_eq_top.1 hπ, Submodule.top_orthogonal_eq_bot]

/-- Continuous linear operators on `H` that agree after right multiplication by every `π a` and
agree on `π.essentialSubspaceᗮ` are equal everywhere on `H`. -/
theorem ext_of_orthogonal_essentialSubspace {S T : H →L[ℂ] H}
    (hmul : ∀ a, S * π a = T * π a) (horth : ∀ ξ ∈ π.essentialSubspaceᗮ, S ξ = T ξ) :
    S = T := by
  -- First establish agreement on the closed essential subspace by linearity and continuity.
  have hspan : ∀ η ∈ Submodule.span ℂ (⋃ a, Set.range (π a)), S η = T η := fun η hη => by
    induction hη using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, v, rfl⟩ := Set.mem_iUnion.1 hx
      exact congr($(hmul a) v)
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  have hess : ∀ η ∈ π.essentialSubspace, S η = T η := fun η hη =>
    isClosed_eq S.continuous T.continuous |>.closure_subset_iff.2 hspan hη
  ext ξ
  have hdecomp : ξ = π.essentialSubspace.starProjection ξ +
      (ξ - π.essentialSubspace.starProjection ξ) := (add_sub_cancel _ _).symm
  rw [hdecomp, map_add, map_add,
    hess _ (π.essentialSubspace.starProjection_apply_mem ξ),
    horth _ (π.essentialSubspace.sub_starProjection_mem_orthogonal ξ)]

variable (π) in
/-- Compression of a representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to its closed essential subspace.
Because `π.essentialSubspace` contains all ranges of `π` and its orthogonal complement is killed by
`π`, this compression is a nondegenerate nonunital star-algebra homomorphism. -/
def restrictEssentialSubspace :
    A →⋆ₙₐ[ℂ] (π.essentialSubspace →L[ℂ] π.essentialSubspace) where
  toFun a := π.essentialSubspace.orthogonalProjectionOnto ∘L π a ∘L π.essentialSubspace.subtypeL
  map_smul' c a := by
    ext ξ
    simp
  map_zero' := by
    ext ξ
    simp
  map_add' a b := by
    ext ξ
    simp
  map_mul' a b := by
    ext ξ
    simp [π.essentialSubspace.starProjection_eq_self_iff.2 (π.apply_mem_essentialSubspace b ξ)]
  map_star' a := by
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      π.essentialSubspace.adjoint_subtypeL, π.essentialSubspace.adjoint_orthogonalProjectionOnto,
      ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]

/-- Operator-composition unfolding of `restrictEssentialSubspace`. -/
theorem restrictEssentialSubspace_def (a : A) :
    π.restrictEssentialSubspace a =
      π.essentialSubspace.orthogonalProjectionOnto ∘L π a ∘L π.essentialSubspace.subtypeL :=
  (rfl)

/-- Coercing `π.restrictEssentialSubspace a ξ` back to `H` gives `π a ξ`. -/
@[simp]
theorem coe_restrictEssentialSubspace_apply (a : A) (ξ : π.essentialSubspace) :
    (π.restrictEssentialSubspace a ξ : H) = π a ξ :=
  π.essentialSubspace.starProjection_eq_self_iff.2 (π.apply_mem_essentialSubspace a ξ)

/-- Extending `π.restrictEssentialSubspace a` by zero on `π.essentialSubspaceᗮ` recovers `π a`. -/
@[simp]
theorem extendByZero_restrictEssentialSubspace (a : A) :
    π.essentialSubspace.extendByZero (π.restrictEssentialSubspace a) = π a :=
  π.essentialSubspace.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL
    (π.apply_mem_essentialSubspace a) fun _ hξ =>
      π.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ a

/-- Composing `π.restrictEssentialSubspace` with `extendByZero` recovers `π`. -/
@[simp]
theorem extendByZero_comp_restrictEssentialSubspace :
    π.essentialSubspace.extendByZero.comp π.restrictEssentialSubspace = π :=
  NonUnitalStarAlgHom.ext π.extendByZero_restrictEssentialSubspace

/-- Compressing `π` to its essential subspace preserves operator norms. -/
@[simp]
theorem norm_restrictEssentialSubspace (a : A) : ‖π.restrictEssentialSubspace a‖ = ‖π a‖ := by
  rw [← π.essentialSubspace.norm_extendByZero, π.extendByZero_restrictEssentialSubspace]

/-- The compression of any representation to its essential subspace is nondegenerate. -/
theorem isNondegenerate_restrictEssentialSubspace :
    π.restrictEssentialSubspace.IsNondegenerate := by
  refine isNondegenerate_iff_forall_apply_eq_zero.2 fun ξ hξ => ?_
  have horth : (ξ : H) ∈ π.essentialSubspaceᗮ :=
    π.mem_orthogonal_essentialSubspace_iff.2 fun a => by
      simpa using congrArg Subtype.val (hξ a)
  exact Subtype.ext <| Submodule.mem_bot ℂ |>.1 <|
    π.essentialSubspace.inf_orthogonal_eq_bot ▸ ⟨ξ.2, horth⟩

end EssentialSubspace

section NonUnitalMultiplierExtension

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

variable (π) in
/-- Canonical extension of a (possibly degenerate) representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to
the multiplier algebra `𝓜(ℂ, A)` on the *same* Hilbert space `H`, obtained by extending the
nondegenerate compression `π.restrictEssentialSubspace` to `𝓜(ℂ, A)` and extending by zero on
`π.essentialSubspaceᗮ`. -/
def nonUnitalMultiplierExtension : 𝓜(ℂ, A) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  π.essentialSubspace.extendByZero.comp
    (π.restrictEssentialSubspace.multiplierExtension
      π.isNondegenerate_restrictEssentialSubspace).toNonUnitalStarAlgHom

/-- Explicit formula for `π.nonUnitalMultiplierExtension` as extension by zero of the multiplier
extension on `π.essentialSubspace`. -/
theorem nonUnitalMultiplierExtension_eq_extendByZero (m : 𝓜(ℂ, A)) :
    π.nonUnitalMultiplierExtension m =
      π.essentialSubspace.extendByZero
        (π.restrictEssentialSubspace.multiplierExtension
          π.isNondegenerate_restrictEssentialSubspace m) :=
  (rfl)

/-- Defining left-multiplication identity for `π.nonUnitalMultiplierExtension`. -/
@[simp]
theorem nonUnitalMultiplierExtension_mul_eq_fst (m : 𝓜(ℂ, A)) (a : A) :
    π.nonUnitalMultiplierExtension m * π a = π (m.fst a) := by
  rw [nonUnitalMultiplierExtension_eq_extendByZero, ← π.extendByZero_restrictEssentialSubspace a,
    ← map_mul, multiplierExtension_mul_eq_fst, π.extendByZero_restrictEssentialSubspace]

/-- Right-multiplication identity for `π.nonUnitalMultiplierExtension`. -/
@[simp]
theorem mul_nonUnitalMultiplierExtension_eq_snd (m : 𝓜(ℂ, A)) (a : A) :
    π a * π.nonUnitalMultiplierExtension m = π (m.snd a) := by
  rw [nonUnitalMultiplierExtension_eq_extendByZero, ← π.extendByZero_restrictEssentialSubspace a,
    ← map_mul, mul_multiplierExtension_eq_snd, π.extendByZero_restrictEssentialSubspace]

/-- `π.nonUnitalMultiplierExtension m` sends `π a ξ` to `π (m.fst a) ξ`. -/
@[simp]
theorem nonUnitalMultiplierExtension_apply_apply (m : 𝓜(ℂ, A)) (a : A) (ξ : H) :
    π.nonUnitalMultiplierExtension m (π a ξ) = π (m.fst a) ξ :=
  congr($(π.nonUnitalMultiplierExtension_mul_eq_fst m a) ξ)

/-- `π.nonUnitalMultiplierExtension m` vanishes on `π.essentialSubspaceᗮ`. -/
theorem nonUnitalMultiplierExtension_apply_eq_zero (m : 𝓜(ℂ, A)) {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) : π.nonUnitalMultiplierExtension m ξ = 0 :=
  π.essentialSubspace.extendByZero_apply_of_mem_orthogonal _ hξ

/-- Every operator `π.nonUnitalMultiplierExtension m` maps `H` into `π.essentialSubspace`. -/
theorem nonUnitalMultiplierExtension_apply_mem_essentialSubspace (m : 𝓜(ℂ, A)) (ξ : H) :
    π.nonUnitalMultiplierExtension m ξ ∈ π.essentialSubspace :=
  π.essentialSubspace.extendByZero_apply_mem _ ξ

/-- Uniqueness characterization of `π.nonUnitalMultiplierExtension m`. -/
theorem eq_nonUnitalMultiplierExtension_iff {m : 𝓜(ℂ, A)} {T : H →L[ℂ] H} :
    T = π.nonUnitalMultiplierExtension m ↔
      (∀ a, T * π a = π (m.fst a)) ∧ (∀ ξ ∈ π.essentialSubspaceᗮ, T ξ = 0) :=
  ⟨fun h => h ▸ ⟨π.nonUnitalMultiplierExtension_mul_eq_fst m,
      fun _ hξ => π.nonUnitalMultiplierExtension_apply_eq_zero m hξ⟩,
    fun ⟨hmul, horth⟩ => π.ext_of_orthogonal_essentialSubspace
      (fun a => by rw [hmul, π.nonUnitalMultiplierExtension_mul_eq_fst])
      (fun ξ hξ => by rw [horth ξ hξ, π.nonUnitalMultiplierExtension_apply_eq_zero m hξ])⟩

/-- `π.nonUnitalMultiplierExtension` restricts to `π` on `A`. -/
@[simp]
theorem nonUnitalMultiplierExtension_coe (a : A) :
    π.nonUnitalMultiplierExtension (a : 𝓜(ℂ, A)) = π a := by
  simp [nonUnitalMultiplierExtension]

/-- `π.nonUnitalMultiplierExtension` sends `1 : 𝓜(ℂ, A)` to the orthogonal projection onto
`π.essentialSubspace`. -/
@[simp]
theorem nonUnitalMultiplierExtension_one :
    π.nonUnitalMultiplierExtension 1 = π.essentialSubspace.starProjection := by
  simp [nonUnitalMultiplierExtension]

/-- Along any increasing approximate unit `e`, `π (m.fst e)` converges strongly on all of `H` to
`π.nonUnitalMultiplierExtension m`. -/
theorem tendsto_nonUnitalMultiplierExtension_apply [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) (ξ : H) :
    Tendsto (fun e => π (m.fst e) ξ) l (𝓝 (π.nonUnitalMultiplierExtension m ξ)) := by
  rw [π.nonUnitalMultiplierExtension_eq_extendByZero, Submodule.extendByZero_apply]
  let u := π.essentialSubspace.orthogonalProjectionOnto ξ
  have hlim := (π.essentialSubspace.subtypeL.continuous.tendsto _).comp
    (tendsto_multiplierExtension_apply π.isNondegenerate_restrictEssentialSubspace hl m u)
  refine hlim.congr fun e => ?_
  calc (π.restrictEssentialSubspace (m.fst e) u : H)
      = π (m.fst e) (π.essentialSubspace.starProjection ξ) +
          π (m.fst e) (ξ - π.essentialSubspace.starProjection ξ) := by
        rw [π.coe_restrictEssentialSubspace_apply,
          π.apply_eq_zero_of_mem_orthogonal_essentialSubspace
            (π.essentialSubspace.sub_starProjection_mem_orthogonal ξ), add_zero]
        rfl
    _ = π (m.fst e) ξ := by rw [← map_add, add_sub_cancel]

/-- Strict left continuity of a norm-bounded family of multipliers implies strong continuity under
`π.nonUnitalMultiplierExtension`. -/
theorem continuous_nonUnitalMultiplierExtension_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).fst a) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C) (ξ : H) :
    Continuous fun x => π.nonUnitalMultiplierExtension (u x) ξ := by
  simp_rw [π.nonUnitalMultiplierExtension_eq_extendByZero, Submodule.extendByZero_apply]
  exact π.essentialSubspace.subtypeL.continuous.comp <|
    continuous_multiplierExtension_apply π.isNondegenerate_restrictEssentialSubspace
      hu hC (π.essentialSubspace.orthogonalProjectionOnto ξ)

/-- When `π` is nondegenerate, `π.nonUnitalMultiplierExtension` agrees with the unital extension
`π.multiplierExtension hπ`. -/
theorem nonUnitalMultiplierExtension_eq_multiplierExtension (hπ : π.IsNondegenerate)
    (m : 𝓜(ℂ, A)) : π.nonUnitalMultiplierExtension m = π.multiplierExtension hπ m :=
  (eq_multiplierExtension_iff hπ).2 (π.nonUnitalMultiplierExtension_mul_eq_fst m)

end NonUnitalMultiplierExtension

section IdealExtension

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Canonical extension of a (possibly degenerate) Hilbert-space representation
`π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a closed two-sided star ideal `I` of `A` to a representation of `A`
on the same Hilbert space `H`. -/
def idealExtension (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  π.nonUnitalMultiplierExtension.comp (I.multiplierHom hmul)

variable {π}

/-- `π.idealExtension hmul` extends `π` on elements of `I`. -/
@[simp]
theorem idealExtension_coe (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (x : I) :
    π.idealExtension hmul (x : A) = π x := by
  simp [idealExtension]

/-- Composing `π.idealExtension hmul` with the subtype inclusion of `I` recovers `π`. -/
@[simp]
theorem idealExtension_comp_subtype (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (π.idealExtension hmul).comp (NonUnitalStarSubalgebraClass.subtype I) = π :=
  NonUnitalStarAlgHom.ext (π.idealExtension_coe hmul)

/-- Left-multiplication formula `(π.idealExtension hmul a) * π x = π ⟨a * x, _⟩`. -/
@[simp]
theorem idealExtension_mul_eq (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    π.idealExtension hmul a * π x = π ⟨a * x, hmul a x x.2⟩ := by
  simp [idealExtension]

/-- Right-multiplication formula `π x * (π.idealExtension hmul a) = π ⟨x * a, _⟩`. -/
@[simp]
theorem mul_idealExtension_eq (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    π x * π.idealExtension hmul a =
      π ⟨x * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2⟩ := by
  simp [idealExtension]

/-- Action of `π.idealExtension hmul a` on vectors of the form `π x ξ`. -/
@[simp]
theorem idealExtension_apply_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) (ξ : H) :
    π.idealExtension hmul a (π x ξ) = π ⟨a * x, hmul a x x.2⟩ ξ := by
  simp [idealExtension]

/-- `π.idealExtension hmul a` vanishes on `π.essentialSubspaceᗮ`. -/
theorem idealExtension_apply_eq_zero (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) : π.idealExtension hmul a ξ = 0 :=
  π.nonUnitalMultiplierExtension_apply_eq_zero _ hξ

/-- Every operator `π.idealExtension hmul a` maps `H` into `π.essentialSubspace`. -/
theorem idealExtension_apply_mem_essentialSubspace (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    (a : A) (ξ : H) : π.idealExtension hmul a ξ ∈ π.essentialSubspace :=
  π.nonUnitalMultiplierExtension_apply_mem_essentialSubspace _ ξ

/-- Uniqueness characterization of `π.idealExtension hmul a` on `H`. -/
theorem eq_idealExtension_iff (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {a : A} {T : H →L[ℂ] H} :
    T = π.idealExtension hmul a ↔
      (∀ x : I, T * π x = π ⟨a * x, hmul a x x.2⟩) ∧ (∀ ξ ∈ π.essentialSubspaceᗮ, T ξ = 0) := by
  rw [idealExtension, NonUnitalStarAlgHom.comp_apply, π.eq_nonUnitalMultiplierExtension_iff]
  simp only [I.multiplierHom_fst_apply]

/-- Extending a representation from a closed ideal preserves its essential subspace. -/
@[simp]
theorem essentialSubspace_idealExtension (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (π.idealExtension hmul).essentialSubspace = π.essentialSubspace := by
  apply le_antisymm
  · exact (π.idealExtension hmul).essentialSubspace_le_iff π.isClosed_essentialSubspace |>.2
      (π.idealExtension_apply_mem_essentialSubspace hmul)
  · exact π.essentialSubspace_le_iff (π.idealExtension hmul).isClosed_essentialSubspace |>.2
      fun x ξ => by
        rw [← π.idealExtension_coe hmul x]
        exact (π.idealExtension hmul).apply_mem_essentialSubspace (x : A) ξ

/-- The extended representation on `A` is nondegenerate if and only if `π` is nondegenerate on
`I`. -/
@[simp]
theorem isNondegenerate_idealExtension_iff (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (π.idealExtension hmul).IsNondegenerate ↔ π.IsNondegenerate := by
  rw [isNondegenerate_iff_essentialSubspace_eq_top, isNondegenerate_iff_essentialSubspace_eq_top,
    π.essentialSubspace_idealExtension hmul]

/-- When `π` is nondegenerate on `I`, `π.idealExtension hmul` is the unique multiplicative map
`A → (H →L[ℂ] H)` extending `π`. -/
theorem eq_idealExtension_of_apply_coe (hπ : π.IsNondegenerate)
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {F : Type*} [FunLike F A (H →L[ℂ] H)]
    [MulHomClass F A (H →L[ℂ] H)] (ψ : F) (hψ : ∀ x : I, ψ x = π x) :
    ⇑ψ = π.idealExtension hmul := by
  funext a
  refine (π.eq_idealExtension_iff hmul).2 ⟨fun x => ?_, fun ξ hξ => ?_⟩
  · rw [← hψ, ← map_mul, ← hψ ⟨a * x, hmul a x x.2⟩]
  · rw [π.orthogonal_essentialSubspace_eq_bot_of_isNondegenerate hπ, Submodule.mem_bot] at hξ
    simp [hξ]

end IdealExtension

end NonUnitalStarAlgHom
