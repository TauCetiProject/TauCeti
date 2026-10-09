/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Ray.Face

/-!
# The fan of projective space

Let `b` be an integral basis of the lattice `N`, indexed by a finite type `ι` of size `n`. The
fan of `n`-dimensional projective space has `n + 1` ray generators: the basis vectors `b j` and
the vector `-∑ j, b j`, which we index by `Option ι`, with `none` for the last one. Its cones are
the cones spanned by the generators indexed by a proper subset `S` of `Option ι`.

Any `n` of the `n + 1` generators form an integral basis, and the only linear relation among all
of them is that they sum to zero. The first fact makes every cone regular. The second makes the
conical coefficients of a point of two such cones agree up to a common constant, which must
vanish since each cone omits a generator. Hence two cones meet in the cone of the intersection
of their index sets, a face of both, and the cones form a fan. It is complete: subtracting from
the coefficients of a point the least of them writes it as a conical combination omitting one
generator.

Classically, the affine chart of the maximal cone omitting the generator indexed by `k` is the
standard affine chart of projective space on which the `k`-th homogeneous coordinate does not
vanish; that identification is not made here.

## Main declarations

* `TauCeti.Toric.projectiveSpaceGenerator`: the ray generators of the fan of projective space.
* `TauCeti.Toric.projectiveSpaceCone`: the cone spanned by the generators indexed by a set.
* `TauCeti.Toric.linearIndepOn_projectiveSpaceGenerator`: any family of generators omitting one
  of them is linearly independent.
* `TauCeti.Toric.projectiveSpaceCone_inf`: the intersection of two cones omitting a generator is
  the cone of the intersection of their index sets.
* `TauCeti.Toric.isRegularCone_projectiveSpaceCone`: each cone omitting a generator is regular.
* `TauCeti.Toric.Fan.projectiveSpace`: the fan of projective space.
* `TauCeti.Toric.Fan.isRegular_projectiveSpace` and
  `TauCeti.Toric.Fan.isComplete_projectiveSpace`: it is regular and complete.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open Set

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  [Fintype ι] (b : Module.Basis ι ℤ N)

/-! ### The ray generators -/

/-- The ray generators of the fan of projective space attached to an integral basis `b`: the
basis vector `b j` at `some j`, and the negative `-∑ j, b j` of their sum at `none`. -/
noncomputable def projectiveSpaceGenerator (k : Option ι) : N :=
  k.elim (-∑ j, b j) b

@[simp]
theorem projectiveSpaceGenerator_none : projectiveSpaceGenerator b none = -∑ j, b j := (rfl)

@[simp]
theorem projectiveSpaceGenerator_some (j : ι) : projectiveSpaceGenerator b (some j) = b j :=
  (rfl)

/-- The ray generators of the fan of projective space sum to zero. -/
theorem sum_projectiveSpaceGenerator : ∑ k, projectiveSpaceGenerator b k = 0 := by
  simp [Fintype.sum_option]

/-- A linear combination of the real ray generators, written in the real basis given by `b`: the
coefficient of `b j` is the difference of the coefficients at `some j` and at `none`. -/
private theorem sum_smul_projectiveSpaceGenerator (c : Option ι → ℝ) :
    ∑ k, c k • i (projectiveSpaceGenerator b k) = ∑ j, (c (some j) - c none) • i (b j) := by
  simp only [Fintype.sum_option, projectiveSpaceGenerator_none, projectiveSpaceGenerator_some,
    map_neg, map_sum, smul_neg, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib]
  abel

/-- Two linear combinations of the real ray generators agree only if their coefficients differ by
a constant: the generators span the real space with the single relation that they sum to zero. -/
private theorem sub_eq_sub_of_sum_smul_eq (hi : IsIntegralLattice i) {c d : Option ι → ℝ}
    (h : ∑ k, c k • i (projectiveSpaceGenerator b k) =
      ∑ k, d k • i (projectiveSpaceGenerator b k)) (k : Option ι) :
    c k - d k = c none - d none := by
  have hB (j : ι) : hi.isBaseChange.basis b j = i (b j) := by
    simpa using hi.isBaseChange.basis_apply b j
  have hli : LinearIndependent ℝ fun j ↦ i (b j) :=
    funext hB ▸ (hi.isBaseChange.basis b).linearIndependent
  rw [sum_smul_projectiveSpaceGenerator, sum_smul_projectiveSpaceGenerator] at h
  cases k with
  | none => rfl
  | some j =>
    have := Fintype.linearIndependent_iffₛ.1 hli _ _ h j
    linarith

/-- Any family of ray generators of the fan of projective space omitting one of them is linearly
independent over the reals. -/
theorem linearIndepOn_projectiveSpaceGenerator (hi : IsIntegralLattice i) {S : Set (Option ι)}
    (hS : S ≠ univ) : LinearIndepOn ℝ (fun k ↦ i (projectiveSpaceGenerator b k)) S := by
  rw [linearIndepOn_iff]
  intro l hlS hl
  rw [Finsupp.mem_supported'] at hlS
  obtain ⟨k, hk⟩ := (ne_univ_iff_exists_notMem S).1 hS
  have h (m : Option ι) : l m - 0 = l none - 0 :=
    sub_eq_sub_of_sum_smul_eq b hi (c := l) (d := 0) (by
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      rw [← hl, Finsupp.linearCombination_apply,
        Finsupp.sum_fintype _ _ fun m ↦ zero_smul ℝ (i (projectiveSpaceGenerator b m))]) m
  ext m
  have := h k
  rw [hlS k hk] at this
  simpa [← this] using h m

/-! ### The cones -/

/-- The cone of the fan of projective space spanned by the ray generators indexed by `S`. It is a
cone of the fan when `S` omits some generator. -/
def projectiveSpaceCone (i : N →+ V) (S : Set (Option ι)) : PointedCone ℝ V :=
  PointedCone.hull ℝ (i '' (projectiveSpaceGenerator b '' S))

theorem projectiveSpaceCone_def (S : Set (Option ι)) :
    projectiveSpaceCone b i S = PointedCone.hull ℝ (i '' (projectiveSpaceGenerator b '' S)) :=
  (rfl)

private theorem projectiveSpaceCone_eq_hull (S : Set (Option ι)) :
    projectiveSpaceCone b i S =
      PointedCone.hull ℝ ((fun k ↦ i (projectiveSpaceGenerator b k)) '' S) := by
  rw [projectiveSpaceCone_def, Set.image_image]

/-- A point lies in the cone of the fan of projective space indexed by `S` exactly when it is a
nonnegative combination of the ray generators with coefficients vanishing outside `S`. -/
theorem mem_projectiveSpaceCone_iff {S : Set (Option ι)} {x : V} :
    x ∈ projectiveSpaceCone b i S ↔ ∃ c : Option ι → ℝ, (∀ k ∉ S, c k = 0) ∧ (∀ k, 0 ≤ c k) ∧
      ∑ k, c k • i (projectiveSpaceGenerator b k) = x := by
  rw [projectiveSpaceCone_eq_hull, PointedCone.mem_hull_image_iff_sum]

@[simp]
theorem projectiveSpaceCone_empty : projectiveSpaceCone b i ∅ = ⊥ := by
  simp [projectiveSpaceCone_def]

theorem projectiveSpaceCone_mono {S T : Set (Option ι)} (h : S ⊆ T) :
    projectiveSpaceCone b i S ≤ projectiveSpaceCone b i T :=
  Submodule.span_mono (image_mono (image_mono h))

/-- Two cones of the fan of projective space, each omitting some generator, meet in the cone of
the intersection of their index sets. -/
theorem projectiveSpaceCone_inf (hi : IsIntegralLattice i) {S T : Set (Option ι)}
    (hS : S ≠ univ) (hT : T ≠ univ) :
    projectiveSpaceCone b i S ⊓ projectiveSpaceCone b i T = projectiveSpaceCone b i (S ∩ T) := by
  refine le_antisymm (fun x ⟨hxS, hxT⟩ ↦ ?_)
    (le_inf (projectiveSpaceCone_mono b inter_subset_left)
      (projectiveSpaceCone_mono b inter_subset_right))
  obtain ⟨c, hcS, hc0, hc⟩ := (mem_projectiveSpaceCone_iff b).1 hxS
  obtain ⟨d, hdT, hd0, hd⟩ := (mem_projectiveSpaceCone_iff b).1 hxT
  have hcd := sub_eq_sub_of_sum_smul_eq b hi (hc.trans hd.symm)
  -- The common difference is `≤ 0` at a generator omitted by `S`, and `≥ 0` at one omitted by `T`.
  obtain ⟨k, hk⟩ := (ne_univ_iff_exists_notMem S).1 hS
  obtain ⟨l, hl⟩ := (ne_univ_iff_exists_notMem T).1 hT
  have hk' := hcd k
  have hl' := hcd l
  rw [hcS k hk] at hk'
  rw [hdT l hl] at hl'
  have hdc (m : Option ι) : d m = c m := by linarith [hcd m, hd0 k, hc0 l]
  refine (mem_projectiveSpaceCone_iff b).2 ⟨c, fun m hm ↦ ?_, hc0, hc⟩
  rcases not_and_or.1 hm with hm | hm
  · exact hcS m hm
  · rw [← hdc m]
    exact hdT m hm

/-- For every index `k` there is an integral basis consisting of the ray generators other than
the one indexed by `k`. -/
private theorem exists_basis_projectiveSpaceGenerator (k : Option ι) :
    ∃ (c : Module.Basis ι ℤ N) (g : ι → Option ι),
      (∀ j, projectiveSpaceGenerator b (g j) = c j) ∧ {k}ᶜ ⊆ range g := by
  classical
  cases k with
  | none =>
    refine ⟨b, some, fun j ↦ rfl, fun m hm ↦ ?_⟩
    cases m with
    | none => exact absurd rfl hm
    | some j => exact ⟨j, rfl⟩
  | some k =>
    -- Replace `b k` by `-∑ j, b j`, through the involution `x ↦ x - (b.coord k x) • u`.
    set u : N := b k + ∑ j, b j with hu
    have hcoord : b.coord k u = 2 := by
      simp [hu, Finsupp.single_apply, Finset.sum_ite_eq', one_add_one_eq_two]
    let L : N →ₗ[ℤ] N := LinearMap.id - (b.coord k).smulRight u
    have hL (x : N) : L x = x - b.coord k x • u := (rfl)
    have hinv : Function.Involutive L := fun x ↦ by
      rw [hL, hL, map_sub, map_smul, hcoord, smul_eq_mul]
      module
    refine ⟨b.map (LinearEquiv.ofInvolutive L hinv), fun j ↦ if j = k then none else some j,
      fun j ↦ ?_, fun m hm ↦ ?_⟩
    · rw [Module.Basis.map_apply, LinearEquiv.coe_ofInvolutive, hL]
      by_cases hj : j = k
      · subst hj
        simp [hu]
      · simp [hj, Ne.symm hj]
    · cases m with
      | none => exact ⟨k, by simp⟩
      | some j =>
        have hj : j ≠ k := fun h ↦ hm (by rw [h, mem_singleton_iff])
        exact ⟨j, by simp [hj]⟩

/-- A cone of the fan of projective space omitting some generator is regular. -/
theorem isRegularCone_projectiveSpaceCone (hi : IsIntegralLattice i) {S : Set (Option ι)}
    (hS : S ≠ univ) : IsRegularCone i (projectiveSpaceCone b i S) := by
  classical
  obtain ⟨k, hk⟩ := (ne_univ_iff_exists_notMem S).1 hS
  obtain ⟨c, g, hgc, hg⟩ := exists_basis_projectiveSpaceGenerator b k
  have hSg : S ⊆ range g := fun m hm ↦ hg fun h ↦ hk (mem_singleton_iff.1 h ▸ hm)
  have himage : projectiveSpaceGenerator b '' S = c '' (g ⁻¹' S) := by
    conv_lhs => rw [← image_preimage_eq_of_subset hSg]
    rw [image_image]
    simp only [hgc]
  rw [projectiveSpaceCone_def, himage]
  exact isRegularCone_hull_image_basis hi c _

/-! ### The fan -/

namespace Fan

/-- The fan of projective space attached to an integral basis `b` of an integral lattice: its
cones are spanned by the families of ray generators `projectiveSpaceGenerator b` omitting at least
one of them. For a basis indexed by a type with `n` elements it is the fan of `n`-dimensional
complex projective space. -/
def projectiveSpace (hi : IsIntegralLattice i) : Fan i where
  lattice := hi
  cones := projectiveSpaceCone b i '' {S | S ≠ univ}
  finite_cones := toFinite _
  isToricCone := by
    rintro _ ⟨S, hS, rfl⟩
    exact (isRegularCone_projectiveSpaceCone b hi hS).toIsToricCone
  mem_of_isFaceOf := by
    rintro _ τ ⟨S, hS, rfl⟩ hτ
    -- A face of a cone is spanned by the generators of the cone that it contains.
    refine ⟨{k | k ∈ S ∧ i (projectiveSpaceGenerator b k) ∈ τ},
      (ne_univ_iff_exists_notMem _).2 ?_, ?_⟩
    · obtain ⟨k, hk⟩ := (ne_univ_iff_exists_notMem S).1 hS
      exact ⟨k, fun h ↦ hk h.1⟩
    have hface := PointedCone.Face.eq_hull_inter_of_eq_hull ⟨τ, hτ⟩ _ (projectiveSpaceCone_def b S)
    refine Eq.trans ?_ hface.symm
    rw [projectiveSpaceCone_def]
    congr 1
    ext x
    simp only [mem_image, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨k, ⟨hkS, hkτ⟩, rfl⟩, rfl⟩
      exact ⟨⟨_, ⟨k, hkS, rfl⟩, rfl⟩, hkτ⟩
    · rintro ⟨⟨_, ⟨k, hkS, rfl⟩, rfl⟩, hkτ⟩
      exact ⟨_, ⟨k, ⟨hkS, hkτ⟩, rfl⟩, rfl⟩
  inf_isFaceOf_left := by
    rintro _ _ ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
    rw [projectiveSpaceCone_inf b hi hS hT, projectiveSpaceCone_eq_hull,
      projectiveSpaceCone_eq_hull]
    -- Inside the cone of `S`, the generators indexed by `S ∩ T` span a face.
    have hli := linearIndepOn_projectiveSpaceGenerator b hi hS
    have h := PointedCone.isFaceOf_hull_image hli
      (C := PointedCone.hull ℝ ((fun k ↦ i (projectiveSpaceGenerator b k)) '' S))
      (by rw [image_eq_range]) {k : S | k.1 ∈ T}
    convert h using 2
    ext x
    simp only [mem_image, mem_inter_iff, mem_ofPred_eq, Subtype.exists, exists_and_right,
      exists_prop]

/-- The cones of the fan of projective space are the cones spanned by the families of ray
generators omitting at least one of them. -/
@[simp]
theorem mem_projectiveSpace_cones (hi : IsIntegralLattice i) {σ : PointedCone ℝ V} :
    σ ∈ (projectiveSpace b hi).cones ↔ ∃ S ≠ univ, projectiveSpaceCone b i S = σ :=
  Iff.rfl

/-- The fan of projective space is regular. -/
theorem isRegular_projectiveSpace (hi : IsIntegralLattice i) :
    (projectiveSpace b hi).IsRegular := by
  rw [isRegular_iff]
  rintro _ ⟨S, hS, rfl⟩
  exact isRegularCone_projectiveSpaceCone b hi hS

/-- The fan of projective space is nonempty: it contains the zero cone. -/
theorem bot_mem_projectiveSpace_cones (hi : IsIntegralLattice i) :
    (⊥ : PointedCone ℝ V) ∈ (projectiveSpace b hi).cones :=
  ⟨∅, (empty_ne_univ : (∅ : Set (Option ι)) ≠ univ), projectiveSpaceCone_empty b⟩

/-- The fan of projective space is complete. -/
theorem isComplete_projectiveSpace (hi : IsIntegralLattice i) :
    (projectiveSpace b hi).IsComplete := by
  -- Subtract the least coefficient of `x`, with coefficient `0` at `none`, from all of them.
  refine (isComplete_iff _).2 fun x ↦ ?_
  let B := hi.isBaseChange.basis b
  have hB (j : ι) : B j = i (b j) := by simpa using hi.isBaseChange.basis_apply b j
  let t : Option ι → ℝ := fun k ↦ k.elim 0 (B.repr x)
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min t
  refine ⟨projectiveSpaceCone b i {k₀}ᶜ,
    ⟨_, (ne_univ_iff_exists_notMem _).2 ⟨k₀, by simp⟩, rfl⟩,
    (mem_projectiveSpaceCone_iff b).2
      ⟨fun k ↦ t k - t k₀, fun k hk ↦ by
        rw [mem_compl_iff, not_not, mem_singleton_iff] at hk
        simp [hk], fun k ↦ sub_nonneg.2 (hk₀ k), ?_⟩⟩
  rw [sum_smul_projectiveSpaceGenerator]
  conv_rhs => rw [← B.sum_repr x]
  simp [t, hB]

end Fan

end TauCeti.Toric
