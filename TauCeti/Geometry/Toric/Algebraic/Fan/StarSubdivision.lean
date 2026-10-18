/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face

import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Star subdivisions of regular cones

Let `τ` be a regular cone with primitive ray generators `u_ρ`, and let `A` be a finite set of rays
of `τ`, spanning the face `σ` of `τ`. The star subdivision of the fan of faces of `τ` along `σ`
uses the ray through `u_A = ∑ ρ ∈ A, u_ρ`, which is a new ray when `A` contains at least two rays;
for `A = {ρ}` it is `ρ` itself, since then `u_A = u_ρ`. Indexing the generators `u_ρ` by `some ρ`
and `u_A` by `none`, its cones are the cones spanned by the generators indexed by a set `S` of
indices which omits `some ρ` for some `ρ ∈ A`. Equivalently, they are the faces of `τ` not
containing `σ`, and the cones spanned by such a face together with `u_A`.

Replacing a generator `u_ρ` with `ρ ∈ A` by `u_A` is a unimodular change of an integral basis
extending the primitive generators of `τ`, so every cone of the star subdivision is regular. The
only linear relations between the generators come from `u_A = ∑ ρ ∈ A, u_ρ`. So the conical
coefficients of a point of two cones of the star subdivision agree, up to adding a common multiple
of that relation, which must vanish since each cone omits a generator indexed by `A`. Hence two
cones meet in the cone of the intersection of their index sets, a face of both. When `A` is
nonempty, the star subdivision covers `τ`: subtracting from the coefficients of a point of `τ`
the least coefficient at a ray of `A`, and putting it on `u_A`, writes the point as a conical
combination omitting a generator indexed by `A`. So it subdivides the fan of faces of `τ`.

The construction of the fan and its face arguments are adapted from those of
`TauCeti.Toric.Fan.projectiveSpace` in `TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Basic`.

Classically, the toric variety of the star subdivision is the blow-up of the affine toric
variety of `τ` along the orbit closure of `σ`.

## Main declarations

* `TauCeti.Toric.starSubdivisionGenerator`: the ray generators of the star subdivision.
* `TauCeti.Toric.starSubdivisionCone`: the cone spanned by the generators indexed by a set.
* `TauCeti.Toric.starSubdivisionCone_inf`: two cones of the star subdivision meet in the cone of
  the intersection of their index sets.
* `TauCeti.Toric.isRegularCone_starSubdivisionCone`: every cone of the star subdivision is
  regular.
* `TauCeti.Toric.Fan.starSubdivision`: the star subdivision of the fan of faces of a regular cone.
* `TauCeti.Toric.Fan.isRegular_starSubdivision`: it is regular.
* `TauCeti.Toric.Fan.starSubdivision_isSubdivision`: for nonempty `A` it subdivides the fan of
  faces of the cone.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3, Definition 3.3.13 and
  Proposition 3.3.15.
-/

public section

open Set

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {τ : PointedCone ℝ V} (hi : IsIntegralLattice i) (A : Finset (ToricRay τ))

/-! ### The ray generators and cones -/

section Generator

variable (hτ : IsToricCone i τ)

/-- The ray generators of the star subdivision of a toric cone `τ` along the rays in `A`: the
primitive generator of `ρ` at `some ρ`, and the sum of the primitive generators of the rays in `A`
at `none`. -/
noncomputable def starSubdivisionGenerator (k : Option (ToricRay τ)) : N :=
  k.elim (∑ ρ ∈ A, primitiveGenerator hi hτ ρ) (primitiveGenerator hi hτ)

@[simp]
theorem starSubdivisionGenerator_none :
    starSubdivisionGenerator hi A hτ none = ∑ ρ ∈ A, primitiveGenerator hi hτ ρ := (rfl)

@[simp]
theorem starSubdivisionGenerator_some (ρ : ToricRay τ) :
    starSubdivisionGenerator hi A hτ (some ρ) = primitiveGenerator hi hτ ρ := (rfl)

/-- The cone of the star subdivision of `τ` along the rays in `A` spanned by the generators
indexed by `S`. It is a cone of the star subdivision when `S` omits `some ρ` for some `ρ ∈ A`. -/
noncomputable def starSubdivisionCone (S : Set (Option (ToricRay τ))) : PointedCone ℝ V :=
  PointedCone.hull ℝ (i '' (starSubdivisionGenerator hi A hτ '' S))

theorem starSubdivisionCone_def (S : Set (Option (ToricRay τ))) :
    starSubdivisionCone hi A hτ S =
      PointedCone.hull ℝ (i '' (starSubdivisionGenerator hi A hτ '' S)) :=
  (rfl)

private theorem starSubdivisionCone_eq_hull (S : Set (Option (ToricRay τ))) :
    starSubdivisionCone hi A hτ S =
      PointedCone.hull ℝ ((fun k ↦ i (starSubdivisionGenerator hi A hτ k)) '' S) := by
  rw [starSubdivisionCone_def, Set.image_image]

/-- A point lies in the cone of the star subdivision indexed by `S` exactly when it is a
nonnegative combination of the ray generators with coefficients vanishing outside `S`. -/
theorem mem_starSubdivisionCone_iff [Fintype (ToricRay τ)] {S : Set (Option (ToricRay τ))}
    {x : V} :
    x ∈ starSubdivisionCone hi A hτ S ↔ ∃ c : Option (ToricRay τ) → ℝ, (∀ k ∉ S, c k = 0) ∧
      (∀ k, 0 ≤ c k) ∧ ∑ k, c k • i (starSubdivisionGenerator hi A hτ k) = x := by
  rw [starSubdivisionCone_eq_hull, PointedCone.mem_hull_image_iff_linearCombination]
  constructor
  · rintro ⟨c, hcS, hc0, rfl⟩
    refine ⟨c, (Finsupp.mem_supported' ℝ c).1 hcS, hc0, ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · rintro ⟨c, hcS, hc0, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm c, (Finsupp.mem_supported' ℝ _).2 hcS, hc0, ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype]

theorem starSubdivisionCone_mono {S T : Set (Option (ToricRay τ))} (h : S ⊆ T) :
    starSubdivisionCone hi A hτ S ≤ starSubdivisionCone hi A hτ T :=
  Submodule.span_mono (image_mono (image_mono h))

/-- Every cone of the star subdivision of `τ` lies in `τ`. -/
theorem starSubdivisionCone_le (S : Set (Option (ToricRay τ))) :
    starSubdivisionCone hi A hτ S ≤ τ := by
  have hu (ρ : ToricRay τ) : i (primitiveGenerator hi hτ ρ) ∈ τ :=
    ρ.1.isFaceOf.le (primitiveGenerator_mem hi hτ ρ)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩
  cases k with
  | none =>
    rw [starSubdivisionGenerator_none, map_sum]
    exact Submodule.sum_mem _ fun ρ _ ↦ hu ρ
  | some ρ => exact hu ρ

/-- A linear combination of the real ray generators of the star subdivision, written in terms of
the primitive generators of `τ`: the coefficient of `u_ρ` is the coefficient at `some ρ`, plus the
coefficient at `none` when `ρ ∈ A`. -/
private theorem sum_smul_starSubdivisionGenerator [Fintype (ToricRay τ)]
    [DecidableEq (ToricRay τ)] (c : Option (ToricRay τ) → ℝ) :
    ∑ k, c k • i (starSubdivisionGenerator hi A hτ k) =
      ∑ ρ, (c (some ρ) + if ρ ∈ A then c none else 0) • i (primitiveGenerator hi hτ ρ) := by
  simp only [Fintype.sum_option, starSubdivisionGenerator_none, starSubdivisionGenerator_some,
    map_sum, Finset.smul_sum, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
    Finset.sum_ite_mem, Finset.univ_inter]
  exact add_comm _ _

end Generator

section Independence

variable (hτ : IsToricCone i τ)

/-- Two linear combinations of the real ray generators of the star subdivision agree only if, at
every ray `ρ`, the coefficient at `some ρ` plus, when `ρ ∈ A`, the coefficient at `none` agree,
provided that the primitive generators of `τ` are linearly independent. -/
private theorem coeff_eq_of_sum_smul_eq
    (hli : LinearIndependent ℝ (fun ρ ↦ i (primitiveGenerator hi hτ ρ)))
    [Fintype (ToricRay τ)] [DecidableEq (ToricRay τ)]
    {c d : Option (ToricRay τ) → ℝ}
    (h : ∑ k, c k • i (starSubdivisionGenerator hi A hτ k) =
      ∑ k, d k • i (starSubdivisionGenerator hi A hτ k)) (ρ : ToricRay τ) :
    c (some ρ) + (if ρ ∈ A then c none else 0) = d (some ρ) + (if ρ ∈ A then d none else 0) := by
  rw [sum_smul_starSubdivisionGenerator, sum_smul_starSubdivisionGenerator] at h
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ h ρ

/-- If the primitive ray generators of a toric cone are linearly independent, then any family of
ray generators of its star subdivision omitting a generator indexed by `A` is linearly independent
over the reals. -/
theorem linearIndepOn_starSubdivisionGenerator
    (hli : LinearIndependent ℝ (fun ρ ↦ i (primitiveGenerator hi hτ ρ)))
    {S : Set (Option (ToricRay τ))}
    (hS : ∃ ρ ∈ A, some ρ ∉ S) :
    LinearIndepOn ℝ (fun k ↦ i (starSubdivisionGenerator hi A hτ k)) S := by
  classical
  have := ToricRay.finite_of_fg hτ.fg
  let _ := Fintype.ofFinite (ToricRay τ)
  rw [linearIndepOn_iff]
  intro l hlS hl
  rw [Finsupp.mem_supported'] at hlS
  obtain ⟨ρ₀, hρ₀A, hρ₀S⟩ := hS
  have h (ρ : ToricRay τ) := coeff_eq_of_sum_smul_eq hi A hτ hli (c := l) (d := 0) (by
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    rw [← hl, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ fun k ↦
        zero_smul ℝ (i (starSubdivisionGenerator hi A hτ k))]) ρ
  have hnone : l none = 0 := by simpa [hρ₀A, hlS _ hρ₀S] using h ρ₀
  ext k
  cases k with
  | none => exact hnone
  | some ρ => simpa [hnone] using h ρ

/-- If the primitive ray generators of a toric cone are linearly independent, then two cones of
its star subdivision, each omitting a generator indexed by `A`, meet in the cone of the intersection
of their index sets. -/
theorem starSubdivisionCone_inf
    (hli : LinearIndependent ℝ (fun ρ ↦ i (primitiveGenerator hi hτ ρ)))
    {S T : Set (Option (ToricRay τ))} (hS : ∃ ρ ∈ A, some ρ ∉ S)
    (hT : ∃ ρ ∈ A, some ρ ∉ T) :
    starSubdivisionCone hi A hτ S ⊓ starSubdivisionCone hi A hτ T =
      starSubdivisionCone hi A hτ (S ∩ T) := by
  classical
  have := ToricRay.finite_of_fg hτ.fg
  let _ := Fintype.ofFinite (ToricRay τ)
  refine le_antisymm (fun x ⟨hxS, hxT⟩ ↦ ?_)
    (le_inf (starSubdivisionCone_mono hi A _ inter_subset_left)
      (starSubdivisionCone_mono hi A _ inter_subset_right))
  obtain ⟨c, hcS, hc0, hc⟩ := (mem_starSubdivisionCone_iff hi A _).1 hxS
  obtain ⟨d, hdT, hd0, hd⟩ := (mem_starSubdivisionCone_iff hi A _).1 hxT
  have hcd := coeff_eq_of_sum_smul_eq hi A hτ hli (hc.trans hd.symm)
  -- The coefficients at `none` agree: compare at a ray of `A` omitted by `S`, and at one omitted
  -- by `T`.
  obtain ⟨ρ₁, hρ₁A, hρ₁S⟩ := hS
  obtain ⟨ρ₂, hρ₂A, hρ₂T⟩ := hT
  have hnone : d none = c none := by
    have h₁ := hcd ρ₁
    have h₂ := hcd ρ₂
    simp only [hρ₁A, hρ₂A, ite_true, hcS _ hρ₁S, hdT _ hρ₂T] at h₁ h₂
    linarith [hc0 (some ρ₂), hd0 (some ρ₁)]
  have hdc (k : Option (ToricRay τ)) : d k = c k := by
    cases k with
    | none => exact hnone
    | some ρ =>
      have := hcd ρ
      split_ifs at this <;> linarith
  refine (mem_starSubdivisionCone_iff hi A _).2 ⟨c, fun k hk ↦ ?_, hc0, hc⟩
  rcases not_and_or.1 hk with hk | hk
  · exact hcS k hk
  · rw [← hdc k]
    exact hdT k hk

end Independence

section Regular

variable (hτ : IsRegularCone i τ)

/-- A cone of the star subdivision of a regular cone omitting a generator indexed by `A` is
regular: replacing that generator by the sum of the generators of `A` in an integral basis
extending the primitive generators of `τ` gives another integral basis. -/
theorem isRegularCone_starSubdivisionCone {S : Set (Option (ToricRay τ))}
    (hS : ∃ ρ ∈ A, some ρ ∉ S) :
    IsRegularCone i (starSubdivisionCone hi A hτ.toIsToricCone S) := by
  classical
  obtain ⟨l, b, hb⟩ := hτ.exists_basis_sum
  have hbu (ρ : ToricRay τ) : b (Sum.inl ρ) = primitiveGenerator hi hτ.toIsToricCone ρ :=
    (hb ρ).eq_primitiveGenerator hi hτ.toIsToricCone
  obtain ⟨ρ₀, hρ₀A, hρ₀S⟩ := hS
  -- The transvection `x ↦ x + (b.coord (inl ρ₀) x) • w` sends `b (inl ρ₀)` to `∑ ρ ∈ A, b (inl ρ)`
  -- and fixes the other basis vectors; it is invertible since `b.coord (inl ρ₀) w = 0`.
  set w : N := ∑ ρ ∈ A, b (Sum.inl ρ) - b (Sum.inl ρ₀) with hw
  have hcw : b.coord (Sum.inl ρ₀) w = 0 := by
    simp [hw, Finsupp.single_apply, hρ₀A]
  have hce (k : ToricRay τ ⊕ Fin l) :
      b.map (LinearEquiv.transvection hcw) k = b k + (if k = Sum.inl ρ₀ then w else 0) := by
    rw [Module.Basis.map_apply, LinearEquiv.transvection.apply]
    simp [Finsupp.single_apply]
  -- The generators indexed by `S` are vectors of the new basis.
  let f : Option (ToricRay τ) → ToricRay τ ⊕ Fin l := fun k ↦ k.elim (Sum.inl ρ₀) Sum.inl
  have himage : starSubdivisionGenerator hi A hτ.toIsToricCone '' S =
      b.map (LinearEquiv.transvection hcw) '' (f '' S) := by
    rw [image_image]
    refine image_congr fun k hk ↦ ?_
    cases k with
    | none =>
      simp only [f, Option.elim, hce]
      simp [hw, hbu]
    | some ρ =>
      have hρ : ρ ≠ ρ₀ := fun h ↦ hρ₀S (h ▸ hk)
      simp only [f, Option.elim, hce]
      simp [hρ, hbu]
  rw [starSubdivisionCone_def, himage]
  exact isRegularCone_hull_image_basis hi _ _

end Regular

/-! ### The fan -/

namespace Fan

variable (hτ : IsRegularCone i τ)

/-- The star subdivision of the fan of faces of a regular cone `τ` along the face spanned by the
rays in `A`: its cones are spanned by the families of ray generators
`starSubdivisionGenerator`, indexed by the sets omitting `some ρ` for some `ρ ∈ A`. It subdivides
the fan of faces of `τ` when `A` is nonempty, and its toric variety is the blow-up of the affine
toric variety of `τ` along the orbit closure of that face. -/
noncomputable def starSubdivision : Fan i where
  lattice := hi
  cones := starSubdivisionCone hi A hτ.toIsToricCone '' {S | ∃ ρ ∈ A, some ρ ∉ S}
  finite_cones := by
    have := ToricRay.finite_of_fg hτ.fg
    exact toFinite _
  isToricCone := by
    rintro _ ⟨S, hS, rfl⟩
    exact (isRegularCone_starSubdivisionCone hi A hτ hS).toIsToricCone
  mem_of_isFaceOf := by
    rintro _ σ ⟨S, hS, rfl⟩ hσ
    -- A face of a cone is spanned by the generators of the cone that it contains.
    refine ⟨{k | k ∈ S ∧ i (starSubdivisionGenerator hi A hτ.toIsToricCone k) ∈ σ}, ?_, ?_⟩
    · obtain ⟨ρ, hρA, hρS⟩ := hS
      exact ⟨ρ, hρA, fun h ↦ hρS h.1⟩
    have hface := PointedCone.Face.eq_hull_image ⟨σ, hσ⟩
      (v := fun k : S ↦ i (starSubdivisionGenerator hi A hτ.toIsToricCone k))
      (by rw [starSubdivisionCone_eq_hull, image_eq_range])
    refine Eq.trans ?_ hface.symm
    rw [starSubdivisionCone_eq_hull]
    congr 1
    ext x
    simp [← PointedCone.Face.mem_toPointedCone, and_comm]
  inf_isFaceOf_left := by
    rintro _ _ ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
    rw [starSubdivisionCone_inf hi A hτ.toIsToricCone
      (hτ.linearIndependent_primitiveGenerator hi) hS hT, starSubdivisionCone_eq_hull,
      starSubdivisionCone_eq_hull]
    -- Inside the cone of `S`, the generators indexed by `S ∩ T` span a face.
    have h := PointedCone.isFaceOf_hull_image
      (linearIndepOn_starSubdivisionGenerator hi A hτ.toIsToricCone
        (hτ.linearIndependent_primitiveGenerator hi) hS)
      (C := PointedCone.hull ℝ
        ((fun k ↦ i (starSubdivisionGenerator hi A hτ.toIsToricCone k)) '' S))
      (by rw [image_eq_range]) {k : S | k.1 ∈ T}
    convert h using 2
    ext x
    simp only [mem_image, mem_inter_iff, mem_ofPred_eq, Subtype.exists, exists_and_right,
      exists_prop]

/-- The cones of the star subdivision of a regular cone along the rays in `A` are the cones spanned
by the families of ray generators omitting a generator indexed by `A`. -/
@[simp]
theorem mem_starSubdivision_cones {σ : PointedCone ℝ V} :
    σ ∈ (starSubdivision hi A hτ).cones ↔
      ∃ S : Set (Option (ToricRay τ)), (∃ ρ ∈ A, some ρ ∉ S) ∧
        starSubdivisionCone hi A hτ.toIsToricCone S = σ :=
  Iff.rfl

/-- The star subdivision of a regular cone is regular. -/
theorem isRegular_starSubdivision : (starSubdivision hi A hτ).IsRegular := by
  rw [isRegular_iff]
  rintro _ ⟨S, hS, rfl⟩
  exact isRegularCone_starSubdivisionCone hi A hτ hS

/-- For nonempty `A`, the ray through the sum of the primitive generators of the rays in `A` is a
cone of the star subdivision. When `A` contains at least two rays, this is the new ray of the star
subdivision; for `A = {ρ}` it is the ray `ρ` itself. -/
theorem hull_singleton_mem_starSubdivision_cones (hA : A.Nonempty) :
    PointedCone.hull ℝ {i (∑ ρ ∈ A, primitiveGenerator hi hτ.toIsToricCone ρ)} ∈
      (starSubdivision hi A hτ).cones := by
  obtain ⟨ρ, hρ⟩ := hA
  exact ⟨{none}, ⟨ρ, hρ, by simp⟩, by simp [starSubdivisionCone_def]⟩

/-- For nonempty `A`, the star subdivision of a regular cone `τ` covers `τ`. -/
@[simp]
theorem support_starSubdivision (hA : A.Nonempty) :
    (starSubdivision hi A hτ).support = (τ : Set V) := by
  classical
  have := ToricRay.finite_of_fg hτ.fg
  let _ := Fintype.ofFinite (ToricRay τ)
  refine Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨_, ⟨S, -, rfl⟩, hxS⟩ := (starSubdivision hi A hτ).mem_support.1 hx
    exact starSubdivisionCone_le hi A hτ.toIsToricCone S hxS
  -- Write `x` as a conical combination of the primitive generators of `τ`, and move the least
  -- coefficient at a ray of `A` onto the sum of the generators of `A`.
  rw [SetLike.mem_coe, ← hτ.toIsToricCone.hull_primitiveGenerator hi, ← range_comp,
    ← image_univ, PointedCone.mem_hull_image_iff_linearCombination] at hx
  obtain ⟨c, -, hc0, rfl⟩ := hx
  obtain ⟨ρ₀, hρ₀A, hρ₀⟩ := A.exists_min_image c hA
  let d : Option (ToricRay τ) → ℝ := fun k ↦ k.elim (c ρ₀) fun ρ ↦ c ρ - if ρ ∈ A then c ρ₀ else 0
  refine (starSubdivision hi A hτ).mem_support.2 ⟨_, ⟨{some ρ₀}ᶜ, ⟨ρ₀, hρ₀A, by simp⟩, rfl⟩,
    (mem_starSubdivisionCone_iff hi A _).2 ⟨d, fun k hk ↦ ?_, fun k ↦ ?_, ?_⟩⟩
  · rw [notMem_compl_iff, mem_singleton_iff] at hk
    simp [hk, d, hρ₀A]
  · cases k with
    | none => exact hc0 ρ₀
    | some ρ =>
      by_cases hρ : ρ ∈ A
      · simpa [d, hρ] using hρ₀ ρ hρ
      · simpa [d, hρ] using hc0 ρ
  · rw [sum_smul_starSubdivisionGenerator, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _
      fun ρ ↦ zero_smul ℝ ((i ∘ primitiveGenerator hi hτ.toIsToricCone) ρ)]
    exact Finset.sum_congr rfl fun ρ _ ↦ by simp [d]

/-- For nonempty `A`, the star subdivision of a regular cone `τ` subdivides the fan of faces of
`τ`. -/
theorem starSubdivision_isSubdivision (hA : A.Nonempty) :
    (starSubdivision hi A hτ).IsSubdivision (ofCone hi hτ.toIsToricCone) where
  exists_cone_le := by
    rintro _ ⟨S, -, rfl⟩
    exact ⟨τ, (mem_ofCone_cones hi _).2 (PointedCone.IsFaceOf.refl τ),
      starSubdivisionCone_le hi A hτ.toIsToricCone S⟩
  support_eq := by rw [support_starSubdivision hi A hτ hA, support_ofCone]

end Fan

end TauCeti.Toric
