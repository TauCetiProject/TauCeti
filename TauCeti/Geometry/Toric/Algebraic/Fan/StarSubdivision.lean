/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face

import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Star subdivisions of regular cones and regular fans

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

The star subdivision of a regular fan `Φ` along one of its cones `σ` is glued from these local
pieces. It keeps the cones of `Φ` not containing `σ`, and replaces each cone `τ` of `Φ` containing
`σ` by the star subdivision of `τ` along the rays of `σ`. These local pieces are compatible: on
a face `τ₀` of `τ` containing `σ`, the star subdivision of `τ` restricts to that of `τ₀`, and a
face of `τ` not containing `σ` is already a cone of the star subdivision of `τ`. So two cones of
the glued family meet in a face of each, inside the intersection of the cones of `Φ` containing
them. When `σ` is nonzero, every cone `τ` containing `σ` is covered by its local piece, so the
result subdivides `Φ`.

A cone of the star subdivision contains the ray through `u_σ` exactly when the least cone of `Φ`
containing it contains `σ`. Indeed, a face of `σ` containing `u_σ` contains every `u_ρ`, so is
`σ`; and a cone omitting `u_σ` is a cone of `Φ` not containing `σ`. This identifies the cones of
the star subdivision lying over the cones containing `σ`, which describes the exceptional divisor
of the blow-down. Dually, the cones of the star subdivision lying over the cones of `Φ` not
containing `σ` are exactly those cones themselves, so away from the exceptional divisor the
blow-down changes nothing.

## Main declarations

* `TauCeti.Toric.starSubdivisionGenerator`: the ray generators of the star subdivision.
* `TauCeti.Toric.starSubdivisionCone`: the cone spanned by the generators indexed by a set.
* `TauCeti.Toric.starSubdivisionCone_inf`: two cones of the star subdivision meet in the cone of
  the intersection of their index sets.
* `TauCeti.Toric.isRegularCone_starSubdivisionCone`: every cone of the star subdivision is
  regular.
* `TauCeti.Toric.starSubdivisionCone_eq_faceOrderIso_symm`: a cone of the star subdivision whose
  index set omits `none` is a face of the cone.
* `TauCeti.Toric.Fan.starSubdivision`: the star subdivision of the fan of faces of a regular cone.
* `TauCeti.Toric.Fan.isRegular_starSubdivision`: it is regular.
* `TauCeti.Toric.Fan.starSubdivision_isSubdivision`: for nonempty `A` it subdivides the fan of
  faces of the cone.
* `TauCeti.Toric.Fan.inf_mem_starSubdivision_cones`: the star subdivision of a regular cone along
  rays of a face restricts to the star subdivision of that face.
* `TauCeti.Toric.Fan.starSubdivisionAlong`: the star subdivision of a regular fan along one of its
  cones, with `TauCeti.Toric.Fan.mem_starSubdivisionAlong_cones` describing its cones.
* `TauCeti.Toric.Fan.isRegular_starSubdivisionAlong` and
  `TauCeti.Toric.Fan.starSubdivisionAlong_isSubdivision`: it is regular, and for a nonzero cone it
  subdivides the fan.
* `TauCeti.Toric.Fan.starSubdivisionAlong_ofCone`: on the fan of faces of a regular cone it is the
  star subdivision of the cone along the rays of the face.
* `TauCeti.Toric.Fan.starSubdivisionAlongRay`: for nonzero `σ`, the ray of the star subdivision
  through `u_σ`.
* `TauCeti.Toric.Fan.starSubdivisionAlongRay_le_starSubdivisionCone`: a cone of the star
  subdivision of a cone `τ ⊇ σ` whose generators include `u_σ` contains the ray through `u_σ`.
* `TauCeti.Toric.Fan.starSubdivisionAlongRay_le_iff_le_leastCone`: a cone of the star subdivision
  contains this ray exactly when the least cone of `Φ` containing it contains `σ`.
* `TauCeti.Toric.Fan.not_le_leastCone_starSubdivisionAlong_iff`: the cones of the star subdivision
  lying over the cones of `Φ` not containing `σ` are those cones themselves.

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

/-- Every ray generator of the star subdivision of `τ` lies in `τ`. -/
theorem starSubdivisionGenerator_mem (k : Option (ToricRay τ)) :
    i (starSubdivisionGenerator hi A hτ k) ∈ τ := by
  have hu (ρ : ToricRay τ) : i (primitiveGenerator hi hτ ρ) ∈ τ :=
    ρ.1.isFaceOf.le (primitiveGenerator_mem hi hτ ρ)
  cases k with
  | none =>
    rw [starSubdivisionGenerator_none, map_sum]
    exact Submodule.sum_mem _ fun ρ _ ↦ hu ρ
  | some ρ => exact hu ρ

/-- Every cone of the star subdivision of `τ` lies in `τ`. -/
theorem starSubdivisionCone_le (S : Set (Option (ToricRay τ))) :
    starSubdivisionCone hi A hτ S ≤ τ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩
  exact starSubdivisionGenerator_mem hi A hτ k

/-- Viewing a set `B` of rays of a face `τ₀` of `τ` as rays of `τ` does not change the ray
generators of the star subdivision along `B`. -/
@[simp]
theorem starSubdivisionGenerator_map_faceEmbedding {τ₀ : PointedCone ℝ V} (h : τ₀.IsFaceOf τ)
    (B : Finset (ToricRay τ₀)) (k : Option (ToricRay τ₀)) :
    starSubdivisionGenerator hi (B.map (ToricRay.faceEmbedding h)) hτ
        (k.map (ToricRay.faceEmbedding h)) =
      starSubdivisionGenerator hi B (hτ.of_isFaceOf h) k := by
  cases k <;> simp [Finset.sum_map]

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

/-- A cone of the star subdivision of a regular cone `τ` whose index set omits `none` is the face
of `τ` spanned by the rays it indexes. -/
theorem starSubdivisionCone_eq_faceOrderIso_symm {S : Set (Option (ToricRay τ))} (hS : none ∉ S) :
    starSubdivisionCone hi A hτ.toIsToricCone S =
      ((hτ.faceOrderIso hi).symm {ρ | some ρ ∈ S}).toPointedCone := by
  rw [IsRegularCone.faceOrderIso_symm_apply_toPointedCone, starSubdivisionCone_def]
  congr 2
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    cases k with
    | none => exact (hS hk).elim
    | some ρ => exact ⟨ρ, hk, rfl⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨some ρ, hρ, rfl⟩

/-- A cone of the star subdivision of a regular cone `τ` whose index set omits `none` is a face
of `τ`. -/
theorem isFaceOf_starSubdivisionCone {S : Set (Option (ToricRay τ))} (hS : none ∉ S) :
    (starSubdivisionCone hi A hτ.toIsToricCone S).IsFaceOf τ := by
  rw [starSubdivisionCone_eq_faceOrderIso_symm hi A hτ hS]
  exact ((hτ.faceOrderIso hi).symm _).isFaceOf

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

/-- Every cone of the star subdivision of a regular cone `τ` lies in `τ`. -/
theorem le_of_mem_starSubdivision_cones {C : PointedCone ℝ V}
    (hC : C ∈ (starSubdivision hi A hτ).cones) : C ≤ τ := by
  obtain ⟨S, -, rfl⟩ := hC
  exact starSubdivisionCone_le hi A hτ.toIsToricCone S

/-- A face of a regular cone `τ` not containing some ray of `A` is a cone of the star subdivision
of `τ` along `A`: it is spanned by the primitive generators of its rays. -/
theorem mem_starSubdivision_cones_of_isFaceOf {F : PointedCone ℝ V} (hF : F.IsFaceOf τ)
    (hA : ∃ ρ ∈ A, ¬ρ.toPointedCone ≤ F) : F ∈ (starSubdivision hi A hτ).cones := by
  refine ⟨some '' {ρ | ρ.toPointedCone ≤ F}, ?_, ?_⟩
  · obtain ⟨ρ, hρA, hρF⟩ := hA
    exact ⟨ρ, hρA, by simpa using hρF⟩
  have h := hτ.faceOrderIso_symm_apply_toPointedCone hi (hτ.faceOrderIso hi ⟨F, hF⟩)
  rw [OrderIso.symm_apply_apply, IsRegularCone.faceOrderIso_apply,
    ToricRay.range_faceEmbedding] at h
  rw [starSubdivisionCone_def, image_image (g := starSubdivisionGenerator hi A hτ.toIsToricCone)]
  exact h.symm

/-- Intersecting with a face `τ₀` of a regular cone `τ` restricts the star subdivision of `τ` along
a set `B` of rays of `τ₀` to the star subdivision of `τ₀` along `B`. -/
theorem inf_mem_starSubdivision_cones {τ₀ C : PointedCone ℝ V} (h : τ₀.IsFaceOf τ)
    (B : Finset (ToricRay τ₀))
    (hC : C ∈ (starSubdivision hi (B.map (ToricRay.faceEmbedding h)) hτ).cones) :
    C ⊓ τ₀ ∈ (starSubdivision hi B (hτ.of_isFaceOf h)).cones := by
  obtain ⟨S, ⟨ρ₀, hρ₀, hρ₀S⟩, rfl⟩ := hC
  obtain ⟨ν₀, hν₀B, rfl⟩ := Finset.mem_map.1 hρ₀
  set e := ToricRay.faceEmbedding h
  set C := starSubdivisionCone hi (B.map e) hτ.toIsToricCone S
  refine ⟨Option.map e ⁻¹' S, ⟨ν₀, hν₀B, by simpa using hρ₀S⟩, ?_⟩
  -- The intersection with `τ₀` is a face of `C`, hence spanned by the generators of `C` it
  -- contains; these are exactly the generators indexed by rays of `τ₀`, and `none`.
  have hface : (C ⊓ τ₀).IsFaceOf C := h.inf_of_le (starSubdivisionCone_le hi _ hτ.toIsToricCone S)
  have hhull : C ⊓ τ₀ = PointedCone.hull ℝ
      (i '' (starSubdivisionGenerator hi (B.map e) hτ.toIsToricCone '' S) ∩ τ₀) := by
    refine (PointedCone.Face.eq_hull_inter_of_eq_hull ⟨_, hface⟩ _
      (starSubdivisionCone_def hi _ hτ.toIsToricCone S)).trans (congrArg _ ?_)
    ext x
    exact and_congr_right fun hx ↦ ⟨fun hx' ↦ hx'.2, fun hx' ↦ ⟨PointedCone.subset_hull hx, hx'⟩⟩
  rw [hhull, starSubdivisionCone_def]
  congr 1
  ext x
  simp only [mem_image, mem_inter_iff, mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    rw [← starSubdivisionGenerator_map_faceEmbedding hi hτ.toIsToricCone h B k]
    refine ⟨⟨_, ⟨_, hk, rfl⟩, rfl⟩, ?_⟩
    rw [starSubdivisionGenerator_map_faceEmbedding]
    exact starSubdivisionGenerator_mem hi B (hτ.toIsToricCone.of_isFaceOf h) k
  · rintro ⟨⟨_, ⟨k, hk, rfl⟩, rfl⟩, hkτ₀⟩
    -- Every generator of `C` lying in `τ₀` is indexed by a ray of `τ₀`, or by `none`.
    obtain ⟨k₀, rfl⟩ : ∃ k₀, Option.map e k₀ = k := by
      cases k with
      | none => exact ⟨none, rfl⟩
      | some ρ =>
        have hρ : ρ ∈ Set.range e := by
          rw [← hτ.faceOrderIso_apply hi ⟨τ₀, h⟩, hτ.mem_faceOrderIso_iff hi]
          rw [← PointedCone.Face.mem_toPointedCone]
          rwa [starSubdivisionGenerator_some] at hkτ₀
        obtain ⟨ν, rfl⟩ := hρ
        exact ⟨some ν, rfl⟩
    exact ⟨_, ⟨k₀, hk, rfl⟩, by rw [starSubdivisionGenerator_map_faceEmbedding]⟩

/-- The star subdivision of a face `τ₀` of a regular cone `τ` along a set `B` of rays of `τ₀`
consists of cones of the star subdivision of `τ` along `B`. -/
theorem mem_starSubdivision_cones_map_faceEmbedding {τ₀ C : PointedCone ℝ V} (h : τ₀.IsFaceOf τ)
    (B : Finset (ToricRay τ₀)) (hC : C ∈ (starSubdivision hi B (hτ.of_isFaceOf h)).cones) :
    C ∈ (starSubdivision hi (B.map (ToricRay.faceEmbedding h)) hτ).cones := by
  obtain ⟨S, ⟨ν, hνB, hνS⟩, rfl⟩ := hC
  let e := ToricRay.faceEmbedding h
  refine ⟨Option.map e '' S, ⟨e ν, Finset.mem_map_of_mem e hνB, ?_⟩, ?_⟩
  · rintro ⟨k, hk, hke⟩
    rw [← Option.map_some (f := e)] at hke
    exact hνS (Option.map_injective e.injective hke ▸ hk)
  · simp only [e, starSubdivisionCone_def, image_image, starSubdivisionGenerator_map_faceEmbedding]

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

/-! ### The star subdivision of a regular fan along a cone -/

namespace Fan

section Along

variable (Φ : Fan i) (hΦ : Φ.IsRegular) {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones)

/-- The star subdivision of the fan of faces of a cone `τ` of `Φ` containing `σ`, along the rays
of `σ`. -/
private noncomputable def starSubdivisionAlongLocal {τ : PointedCone ℝ V} (hτ : τ ∈ Φ.cones)
    (hστ : σ ≤ τ) : Fan i :=
  starSubdivision Φ.lattice
    (ToricRay.faceFinset (Φ.isFaceOf_of_le hτ hσ hστ) (Φ.isToricCone hσ).fg)
    (isRegular_iff.1 hΦ _ hτ)

/-- The cones of the star subdivision of `Φ` along `σ`: the cones of `Φ` not containing `σ`, and
the cones of the star subdivisions of the cones of `Φ` containing `σ`. -/
private noncomputable def starSubdivisionAlongCones : Set (PointedCone ℝ V) :=
  {C | C ∈ Φ.cones ∧ ¬σ ≤ C} ∪
    ⋃ (τ) (hτ : τ ∈ Φ.cones) (hστ : σ ≤ τ), (starSubdivisionAlongLocal Φ hΦ hσ hτ hστ).cones

private theorem mem_starSubdivisionAlongCones {C : PointedCone ℝ V} :
    C ∈ starSubdivisionAlongCones Φ hΦ hσ ↔ (C ∈ Φ.cones ∧ ¬σ ≤ C) ∨
      ∃ τ, ∃ (hτ : τ ∈ Φ.cones) (hστ : σ ≤ τ),
        C ∈ (starSubdivisionAlongLocal Φ hΦ hσ hτ hστ).cones := by
  simp [starSubdivisionAlongCones]

/-- Two cones of `Φ` containing `σ` meet in a cone containing `σ`, and the star subdivisions of the
two restrict to the star subdivision of their intersection. -/
private theorem starSubdivisionAlongLocal_inf_isFaceOf {τ₁ τ₂ C D : PointedCone ℝ V}
    (hτ₁ : τ₁ ∈ Φ.cones) (hστ₁ : σ ≤ τ₁) (hτ₂ : τ₂ ∈ Φ.cones) (hστ₂ : σ ≤ τ₂)
    (hC : C ∈ (starSubdivisionAlongLocal Φ hΦ hσ hτ₁ hστ₁).cones)
    (hD : D ∈ (starSubdivisionAlongLocal Φ hΦ hσ hτ₂ hστ₂).cones) :
    (C ⊓ D).IsFaceOf C := by
  have hτ₀ := Φ.inf_mem hτ₁ hτ₂
  have hστ₀ : σ ≤ τ₁ ⊓ τ₂ := le_inf hστ₁ hστ₂
  have h₁ := Φ.inf_isFaceOf_left hτ₁ hτ₂
  have h₂ := Φ.inf_isFaceOf_right hτ₁ hτ₂
  have hσ₀ := Φ.isFaceOf_of_le hτ₀ hσ hστ₀
  -- Both cones restrict to cones of the star subdivision of `τ₁ ⊓ τ₂`.
  have hC₀ : C ⊓ (τ₁ ⊓ τ₂) ∈ (starSubdivisionAlongLocal Φ hΦ hσ hτ₀ hστ₀).cones := by
    rw [starSubdivisionAlongLocal, ToricRay.faceFinset_eq_map h₁ hσ₀] at hC
    exact inf_mem_starSubdivision_cones Φ.lattice (isRegular_iff.1 hΦ _ hτ₁) h₁ _ hC
  have hD₀ : D ⊓ (τ₁ ⊓ τ₂) ∈ (starSubdivisionAlongLocal Φ hΦ hσ hτ₀ hστ₀).cones := by
    rw [starSubdivisionAlongLocal, ToricRay.faceFinset_eq_map h₂ hσ₀] at hD
    exact inf_mem_starSubdivision_cones Φ.lattice (isRegular_iff.1 hΦ _ hτ₂) h₂ _ hD
  have hCτ₁ := le_of_mem_starSubdivision_cones _ _ _ hC
  have hDτ₂ := le_of_mem_starSubdivision_cones _ _ _ hD
  have hCD : C ⊓ (τ₁ ⊓ τ₂) ⊓ (D ⊓ (τ₁ ⊓ τ₂)) = C ⊓ D := by
    rw [inf_inf_inf_comm, inf_idem,
      inf_eq_left.2 (le_inf (inf_le_left.trans hCτ₁) (inf_le_right.trans hDτ₂))]
  exact hCD ▸ ((starSubdivisionAlongLocal Φ hΦ hσ hτ₀ hστ₀).inf_isFaceOf_left hC₀ hD₀).trans
    (h₁.inf_of_le hCτ₁)

/-- A cone of `Φ` not containing `σ` meets a cone `τ` of `Φ` containing `σ` in a face of `τ` not
containing `σ`, which is a cone of the star subdivision of `τ`. -/
private theorem inf_mem_starSubdivisionAlongLocal {τ D : PointedCone ℝ V} (hτ : τ ∈ Φ.cones)
    (hστ : σ ≤ τ) (hD : D ∈ Φ.cones) (hσD : ¬σ ≤ D) :
    τ ⊓ D ∈ (starSubdivisionAlongLocal Φ hΦ hσ hτ hστ).cones :=
  mem_starSubdivision_cones_of_isFaceOf _ _ _ (Φ.inf_isFaceOf_left hτ hD)
    (ToricRay.exists_mem_faceFinset_not_le_of_not_le _ _ (Φ.isToricCone hσ).salient
      fun h ↦ hσD (h.trans inf_le_right))

private theorem starSubdivisionAlongCones_inf_isFaceOf {C D : PointedCone ℝ V}
    (hC : C ∈ starSubdivisionAlongCones Φ hΦ hσ) (hD : D ∈ starSubdivisionAlongCones Φ hΦ hσ) :
    (C ⊓ D).IsFaceOf C := by
  rw [mem_starSubdivisionAlongCones] at hC hD
  rcases hC with ⟨hC, hσC⟩ | ⟨τ₁, hτ₁, hστ₁, hC⟩ <;>
    rcases hD with ⟨hD, hσD⟩ | ⟨τ₂, hτ₂, hστ₂, hD⟩
  · exact Φ.inf_isFaceOf_left hC hD
  · -- `C ⊓ D = (τ₂ ⊓ C) ⊓ D` is a face of the face `τ₂ ⊓ C` of `C`.
    have hF := inf_mem_starSubdivisionAlongLocal Φ hΦ hσ hτ₂ hστ₂ hC hσC
    have h := ((starSubdivisionAlongLocal Φ hΦ hσ hτ₂ hστ₂).inf_isFaceOf_left hF hD).trans
      (Φ.inf_isFaceOf_right hτ₂ hC)
    rwa [inf_comm τ₂, inf_assoc, inf_eq_right.2 (le_of_mem_starSubdivision_cones _ _ _ hD)] at h
  · -- `C ⊓ D = C ⊓ (τ₁ ⊓ D)`, and `τ₁ ⊓ D` is a cone of the star subdivision of `τ₁`.
    have hF := inf_mem_starSubdivisionAlongLocal Φ hΦ hσ hτ₁ hστ₁ hD hσD
    have h := (starSubdivisionAlongLocal Φ hΦ hσ hτ₁ hστ₁).inf_isFaceOf_left hC hF
    rwa [← inf_assoc, inf_eq_left.2 (le_of_mem_starSubdivision_cones _ _ _ hC)] at h
  · exact starSubdivisionAlongLocal_inf_isFaceOf Φ hΦ hσ hτ₁ hστ₁ hτ₂ hστ₂ hC hD

/-- The *star subdivision* of a regular fan `Φ` along one of its cones `σ`. It keeps the cones of
`Φ` not containing `σ`, and replaces every cone `τ` of `Φ` containing `σ` by the cones of the star
subdivision of `τ` along the rays of `σ`, `TauCeti.Toric.Fan.starSubdivision`. These cones use the
ray through `u_σ = ∑ ρ, u_ρ`, the sum of the primitive generators of the rays of `σ`. For `σ`
nonzero this subdivides `Φ`, and classically its toric variety is the blow-up of that of `Φ` along
the orbit closure of `σ`. For `σ = ⊥` the vector `u_σ` vanishes and the construction degenerates,
so the subdivision theorems assume `σ ≠ ⊥`. -/
noncomputable def starSubdivisionAlong : Fan i where
  lattice := Φ.lattice
  cones := starSubdivisionAlongCones Φ hΦ hσ
  finite_cones := by
    refine (Φ.finite_cones.subset (sep_subset _ _)).union ?_
    refine Φ.finite_cones.biUnion' fun τ hτ ↦ ?_
    exact finite_iUnion fun hστ ↦ (starSubdivisionAlongLocal Φ hΦ hσ hτ hστ).finite_cones
  isToricCone C hC := by
    rcases (mem_starSubdivisionAlongCones Φ hΦ hσ).1 hC with ⟨hC, -⟩ | ⟨τ, hτ, hστ, hC⟩
    · exact Φ.isToricCone hC
    · exact (starSubdivisionAlongLocal Φ hΦ hσ hτ hστ).isToricCone hC
  mem_of_isFaceOf C F hC hF := by
    rw [mem_starSubdivisionAlongCones] at hC ⊢
    rcases hC with ⟨hC, hσC⟩ | ⟨τ, hτ, hστ, hC⟩
    · exact Or.inl (Φ.setOf_not_le_closedUnderFaces σ ⟨hC, hσC⟩ hF)
    · exact Or.inr ⟨τ, hτ, hστ, (starSubdivisionAlongLocal Φ hΦ hσ hτ hστ).mem_of_isFaceOf hC hF⟩
  inf_isFaceOf_left _ _ := starSubdivisionAlongCones_inf_isFaceOf Φ hΦ hσ

/-- The cones of the star subdivision of a regular fan `Φ` along its cone `σ` are the cones of `Φ`
not containing `σ`, and the cones of the star subdivisions of the cones `τ` of `Φ` containing `σ`
along the rays of `σ`. -/
@[simp]
theorem mem_starSubdivisionAlong_cones {C : PointedCone ℝ V} :
    C ∈ (Φ.starSubdivisionAlong hΦ hσ).cones ↔ (C ∈ Φ.cones ∧ ¬σ ≤ C) ∨
      ∃ τ, ∃ (hτ : τ ∈ Φ.cones) (hστ : σ ≤ τ), C ∈ (starSubdivision Φ.lattice
        (ToricRay.faceFinset (Φ.isFaceOf_of_le hτ hσ hστ) (Φ.isToricCone hσ).fg)
        (isRegular_iff.1 hΦ _ hτ)).cones :=
  mem_starSubdivisionAlongCones Φ hΦ hσ

/-- A cone of `Φ` not containing `σ` is a cone of the star subdivision of `Φ` along `σ`. -/
theorem mem_starSubdivisionAlong_cones_of_not_le {C : PointedCone ℝ V} (hC : C ∈ Φ.cones)
    (hσC : ¬σ ≤ C) : C ∈ (Φ.starSubdivisionAlong hΦ hσ).cones :=
  (mem_starSubdivisionAlong_cones Φ hΦ hσ).2 (Or.inl ⟨hC, hσC⟩)

/-- Every cone of the star subdivision of `Φ` along `σ` lies in a cone of `Φ`. -/
theorem exists_cone_le_of_mem_starSubdivisionAlong_cones {C : PointedCone ℝ V}
    (hC : C ∈ (Φ.starSubdivisionAlong hΦ hσ).cones) : ∃ τ ∈ Φ.cones, C ≤ τ := by
  rcases (mem_starSubdivisionAlong_cones Φ hΦ hσ).1 hC with ⟨hC, -⟩ | ⟨τ, hτ, _, hC⟩
  · exact ⟨C, hC, le_rfl⟩
  · exact ⟨τ, hτ, le_of_mem_starSubdivision_cones _ _ _ hC⟩

/-- The star subdivision of a regular fan along one of its cones is regular. -/
theorem isRegular_starSubdivisionAlong : (Φ.starSubdivisionAlong hΦ hσ).IsRegular := by
  rw [isRegular_iff]
  intro C hC
  rcases (mem_starSubdivisionAlong_cones Φ hΦ hσ).1 hC with ⟨hC, -⟩ | ⟨τ, hτ, _, hC⟩
  · exact isRegular_iff.1 hΦ _ hC
  · exact isRegular_iff.1 (isRegular_starSubdivision _ _ _) _ hC

/-- The star subdivision of a regular fan `Φ` along a nonzero cone of `Φ` has the same support as
`Φ`. -/
@[simp]
theorem support_starSubdivisionAlong (hσ0 : σ ≠ ⊥) :
    (Φ.starSubdivisionAlong hΦ hσ).support = Φ.support := by
  refine Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨C, hC, hxC⟩ := (Φ.starSubdivisionAlong hΦ hσ).mem_support.1 hx
    obtain ⟨τ, hτ, hCτ⟩ := Φ.exists_cone_le_of_mem_starSubdivisionAlong_cones hΦ hσ hC
    exact Φ.subset_support hτ (hCτ hxC)
  obtain ⟨τ, hτ, hxτ⟩ := Φ.mem_support.1 hx
  by_cases hστ : σ ≤ τ
  · -- The star subdivision of `τ` along the rays of `σ` covers `τ`, since `σ` has a ray.
    have hστ' := Φ.isFaceOf_of_le hτ hσ hστ
    have hA :=
      ToricRay.faceFinset_nonempty hστ' (Φ.isToricCone hσ).fg (Φ.isToricCone hσ).salient hσ0
    have hx' : x ∈ (starSubdivision Φ.lattice (ToricRay.faceFinset hστ' (Φ.isToricCone hσ).fg)
        (isRegular_iff.1 hΦ _ hτ)).support := by
      rwa [support_starSubdivision Φ.lattice _ _ hA]
    obtain ⟨C, hC, hxC⟩ := (mem_support _).1 hx'
    exact (Φ.starSubdivisionAlong hΦ hσ).subset_support
      ((mem_starSubdivisionAlong_cones Φ hΦ hσ).2 (Or.inr ⟨τ, hτ, hστ, hC⟩)) hxC
  · exact (Φ.starSubdivisionAlong hΦ hσ).subset_support
      (Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ hσ hτ hστ) hxτ

/-- The star subdivision of a regular fan along a nonzero cone of the fan subdivides it. -/
theorem starSubdivisionAlong_isSubdivision (hσ0 : σ ≠ ⊥) :
    (Φ.starSubdivisionAlong hΦ hσ).IsSubdivision Φ where
  exists_cone_le _ := Φ.exists_cone_le_of_mem_starSubdivisionAlong_cones hΦ hσ
  support_eq := Φ.support_starSubdivisionAlong hΦ hσ hσ0

/-- On the fan of faces of a regular cone `τ`, the star subdivision along a face `σ` of `τ` is the
star subdivision of `τ` along the rays of `σ`. -/
theorem starSubdivisionAlong_ofCone (hi : IsIntegralLattice i) {τ : PointedCone ℝ V}
    (hτ : IsRegularCone i τ) (hσ : σ ∈ (ofCone hi hτ.toIsToricCone).cones) :
    (ofCone hi hτ.toIsToricCone).starSubdivisionAlong (isRegular_ofCone hi hτ) hσ =
      starSubdivision hi (ToricRay.faceFinset ((mem_ofCone_cones hi _).1 hσ)
        (hτ.toIsToricCone.of_isFaceOf ((mem_ofCone_cones hi _).1 hσ)).fg) hτ := by
  have hστ := (mem_ofCone_cones hi _).1 hσ
  ext C
  rw [mem_starSubdivisionAlong_cones]
  refine ⟨?_, fun hC ↦ Or.inr ⟨τ, (mem_ofCone_cones hi _).2 (PointedCone.IsFaceOf.refl τ),
    hστ.le, hC⟩⟩
  rintro (⟨hC, hσC⟩ | ⟨τ₀, hτ₀, _, hC⟩)
  · exact mem_starSubdivision_cones_of_isFaceOf hi _ hτ ((mem_ofCone_cones hi _).1 hC)
      (ToricRay.exists_mem_faceFinset_not_le_of_not_le _ _
        (hτ.toIsToricCone.of_isFaceOf hστ).salient hσC)
  · -- A cone of the star subdivision of a face `τ₀` of `τ` containing `σ` is one for `τ`.
    have hτ₀τ := (mem_ofCone_cones hi _).1 hτ₀
    have h := mem_starSubdivision_cones_map_faceEmbedding hi hτ hτ₀τ _ hC
    rwa [← ToricRay.faceFinset_eq_map hτ₀τ] at h

/-! ### The ray through the sum of the primitive generators -/

/-- Inside every cone `τ` of `Φ` containing `σ`, the star subdivision along `σ` uses the same new
ray generator: the sum of the primitive generators of the rays of `σ`. -/
private theorem starSubdivisionGenerator_none_faceFinset {τ : PointedCone ℝ V}
    (hτ : τ ∈ Φ.cones) (hστ : σ ≤ τ) :
    starSubdivisionGenerator Φ.lattice
        (ToricRay.faceFinset (Φ.isFaceOf_of_le hτ hσ hστ) (Φ.isToricCone hσ).fg)
        (Φ.isToricCone hτ) none =
      ∑ ρ ∈ ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) (Φ.isToricCone hσ).fg,
        primitiveGenerator Φ.lattice (Φ.isToricCone hσ) ρ := by
  rw [ToricRay.faceFinset_eq_map (Φ.isFaceOf_of_le hτ hσ hστ) (PointedCone.IsFaceOf.refl σ),
    ← Option.map_none (f := ToricRay.faceEmbedding (Φ.isFaceOf_of_le hτ hσ hστ)),
    starSubdivisionGenerator_map_faceEmbedding, starSubdivisionGenerator_none]

/-- The ray of the star subdivision of `Φ` along a nonzero cone `σ` through the sum `u_σ` of the
primitive generators of the rays of `σ`. When `σ` has at least two rays this is the ray added by
the star subdivision; when `σ` is a ray it is `σ` itself. -/
noncomputable def starSubdivisionAlongRay (hσ0 : σ ≠ ⊥) : (Φ.starSubdivisionAlong hΦ hσ).Ray :=
  have hA := ToricRay.faceFinset_nonempty (PointedCone.IsFaceOf.refl σ) (Φ.isToricCone hσ).fg
    (Φ.isToricCone hσ).salient hσ0
  ⟨⟨PointedCone.hull ℝ {i (∑ ρ ∈ ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ)
      (Φ.isToricCone hσ).fg, primitiveGenerator Φ.lattice (Φ.isToricCone hσ) ρ)},
    (Φ.mem_starSubdivisionAlong_cones hΦ hσ).2 (Or.inr ⟨σ, hσ, le_rfl,
      hull_singleton_mem_starSubdivision_cones Φ.lattice _ (isRegular_iff.1 hΦ _ hσ) hA⟩)⟩, by
    obtain ⟨ρ, hρ⟩ := hA
    have h := (linearIndepOn_starSubdivisionGenerator Φ.lattice _ (Φ.isToricCone hσ)
      ((isRegular_iff.1 hΦ _ hσ).linearIndependent_primitiveGenerator Φ.lattice)
      (S := {none}) ⟨ρ, hρ, by simp⟩).ne_zero (mem_singleton none)
    rw [starSubdivisionGenerator_none] at h
    exact PointedCone.finrank_span_coe_hull_singleton h⟩

/-- The cone of `Fan.starSubdivisionAlongRay` is the ray through the sum of the primitive generators
of the rays of `σ`. -/
@[simp]
theorem coe_toCone_starSubdivisionAlongRay (hσ0 : σ ≠ ⊥) :
    ((Φ.starSubdivisionAlongRay hΦ hσ hσ0).toCone : PointedCone ℝ V) =
      PointedCone.hull ℝ {i (∑ ρ ∈ ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ)
        (Φ.isToricCone hσ).fg, primitiveGenerator Φ.lattice (Φ.isToricCone hσ) ρ)} :=
  (rfl)

/-- A cone of the star subdivision of a cone `τ ⊇ σ` of `Φ` along the rays of `σ` whose generators
include `u_σ` contains the ray through `u_σ`. -/
theorem starSubdivisionAlongRay_le_starSubdivisionCone (hσ0 : σ ≠ ⊥) {τ : PointedCone ℝ V}
    (hτ : τ ∈ Φ.cones) (hστ : σ ≤ τ) {S : Set (Option (ToricRay τ))} (hS : none ∈ S) :
    ((Φ.starSubdivisionAlongRay hΦ hσ hσ0).toCone : PointedCone ℝ V) ≤
      starSubdivisionCone Φ.lattice
        (ToricRay.faceFinset (Φ.isFaceOf_of_le hτ hσ hστ) (Φ.isToricCone hσ).fg)
        (Φ.isToricCone hτ) S := by
  rw [coe_toCone_starSubdivisionAlongRay, Submodule.span_singleton_le_iff_mem,
    ← starSubdivisionGenerator_none_faceFinset Φ hσ hτ hστ]
  exact PointedCone.subset_hull ⟨_, ⟨none, hS, rfl⟩, rfl⟩

/-- A cone of the star subdivision of `Φ` along a nonzero cone `σ` contains the ray through
`u_σ` exactly when the least cone of `Φ` containing it contains `σ`. -/
theorem starSubdivisionAlongRay_le_iff_le_leastCone (hσ0 : σ ≠ ⊥)
    (C : (Φ.starSubdivisionAlong hΦ hσ).cones) :
    (Φ.starSubdivisionAlongRay hΦ hσ hσ0).toCone ≤ C ↔
      σ ≤ (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.leastCone C.2 := by
  have hsub := Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0
  have hσt := Φ.isToricCone hσ
  constructor
  · intro hu
    rw [← Subtype.coe_le_coe, coe_toCone_starSubdivisionAlongRay,
      Submodule.span_singleton_le_iff_mem] at hu
    -- The face `σ ⊓ L` of `σ` contains `u_σ`, hence contains `σ`.
    exact (hσt.le_of_isFaceOf_of_sum_primitiveGenerator_mem Φ.lattice
      (Φ.inf_isFaceOf_left hσ (hsub.toFanHom.leastCone_mem C.2))
      ⟨starSubdivisionGenerator_mem Φ.lattice _ hσt none, hsub.le_leastCone C.2 hu⟩).trans
        inf_le_right
  · intro hσL
    obtain ⟨C, hC⟩ := C
    rcases (Φ.mem_starSubdivisionAlong_cones hΦ hσ).1 hC with ⟨hCΦ, hσC⟩ | ⟨τ, hτ, hστ, hCτ⟩
    · exact (hσC (hσL.trans (hsub.leastCone_eq_self hC hCΦ).le)).elim
    obtain ⟨S, ⟨ρ₀, hρ₀A, hρ₀S⟩, rfl⟩ := hCτ
    by_cases hS : none ∈ S
    · exact Φ.starSubdivisionAlongRay_le_starSubdivisionCone hΦ hσ hσ0 hτ hστ hS
    -- Otherwise the cone is the face of `τ` spanned by rays of `τ`, which misses `ρ₀`.
    have hτr := isRegular_iff.1 hΦ _ hτ
    have hface := starSubdivisionCone_eq_faceOrderIso_symm Φ.lattice
      (ToricRay.faceFinset (Φ.isFaceOf_of_le hτ hσ hστ) hσt.fg) hτr hS
    have hσC := hσL.trans (hsub.leastCone_eq_self hC (Φ.mem_of_isFaceOf hτ
      (isFaceOf_starSubdivisionCone Φ.lattice _ hτr hS))).le
    rw [hface] at hσC
    have hρ₀ := (hτr.mem_faceOrderIso_iff Φ.lattice _ ρ₀).2 (hσC (((ToricRay.mem_faceFinset _ _).1
      hρ₀A) (primitiveGenerator_mem Φ.lattice hτr.toIsToricCone ρ₀)))
    rw [OrderIso.apply_symm_apply] at hρ₀
    exact (hρ₀S hρ₀).elim

/-- Away from the cones containing `σ` the star subdivision of `Φ` along a nonzero cone `σ` changes
nothing: a cone of the star subdivision has a least cone in `Φ` not containing `σ` exactly when it
is a cone of `Φ` not containing `σ`. -/
theorem not_le_leastCone_starSubdivisionAlong_iff (hσ0 : σ ≠ ⊥) {C : PointedCone ℝ V}
    (hC : C ∈ (Φ.starSubdivisionAlong hΦ hσ).cones) :
    ¬σ ≤ (Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0).toFanHom.leastCone hC ↔
      C ∈ Φ.cones ∧ ¬σ ≤ C := by
  have hsub := Φ.starSubdivisionAlong_isSubdivision hΦ hσ hσ0
  constructor
  · intro hσL
    refine ⟨?_, fun h ↦ hσL (h.trans (hsub.le_leastCone hC))⟩
    rcases (Φ.mem_starSubdivisionAlong_cones hΦ hσ).1 hC with
      ⟨hCΦ, -⟩ | ⟨τ, hτ, hστ, S, -, rfl⟩
    · exact hCΦ
    by_cases hS : none ∈ S
    · -- The cone contains the ray through `u_σ`, so its least cone contains `σ`.
      exact (hσL ((Φ.starSubdivisionAlongRay_le_iff_le_leastCone hΦ hσ hσ0 ⟨_, hC⟩).1
        (Φ.starSubdivisionAlongRay_le_starSubdivisionCone hΦ hσ hσ0 hτ hστ hS))).elim
    · exact Φ.mem_of_isFaceOf hτ
        (isFaceOf_starSubdivisionCone Φ.lattice _ (isRegular_iff.1 hΦ _ hτ) hS)
  · rintro ⟨hCΦ, hσC⟩
    rwa [hsub.leastCone_eq_self hC hCΦ]

end Along

end Fan

end TauCeti.Toric
