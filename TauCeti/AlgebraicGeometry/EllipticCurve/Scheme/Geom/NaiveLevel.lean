/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.RationalPoint.Basic

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ZModProdAut
import TauCeti.AlgebraicGeometry.IdealSheaf.Section

/-!
# Naive level structures on an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `A` a group. A homomorphism `φ : A →* E(S)` to
the group of `S`-points of `E` is **injective on every fibre**
(`EllipticCurveGeom.IsFiberwiseInjective`) when for every `a ≠ 1` in `A` the section `φ a` misses
the zero section at every point of `S`. Equivalently, for every point `s` of `S`, the composite of
`φ` with restriction to the fibre of `E` over the residue field `κ(s)` is injective
(`EllipticCurveGeom.isFiberwiseInjective_iff_forall_residueField`), and then so is its composite
with restriction to the fibre over any field-valued point of `S`, in particular over every geometric
point (`EllipticCurveGeom.IsFiberwiseInjective.injective_pointsPullback`).

For `A = ℤ/Nℤ` with `N ≠ 0` such a homomorphism is an `S`-point `P` of `E[N]` that has exact order
`N` in every geometric fibre: none of `P, 2P, …, (N - 1)P` meets the zero section
(`EllipticCurveGeom.isFiberwiseInjective_zmod_iff`). For `A = (ℤ/Nℤ)²` it is a pair `(P, Q)` of
`S`-points of `E[N]` none of whose combinations `aP + bQ` with `(a, b) ≠ 0` meets the zero section
(`EllipticCurveGeom.isFiberwiseInjective_zmod_prod_iff`), that is, a basis of the `N`-torsion in
every geometric fibre in which `N` is invertible: over a separably closed field in which `N` is
invertible, the injective homomorphisms `(ℤ/Nℤ)² →* E(K)` are exactly those with image `E[N](K)`
(`EllipticCurveGeom.isFiberwiseInjective_iff_range_eq_ker`), every elliptic curve there has
one (`EllipticCurveGeom.exists_isFiberwiseInjective`), and any two differ by a unique matrix in
`GL₂(ℤ/Nℤ)` acting on `(ℤ/Nℤ)²` (`EllipticCurveGeom.IsFiberwiseInjective.existsUnique_eq_comp`).
Over a base on which `N` is invertible these are the naive `[Γ₁(N)]`- and `[Γ(N)]`-structures,
which are compared with Drinfeld level structures in Katz–Mazur §3.7.

The condition is pointwise, so it is stable under arbitrary base change
(`EllipticCurveGeom.IsFiberwiseInjective.pointsPullback`), and it descends along surjective base
changes (`EllipticCurveGeom.isFiberwiseInjective_pointsPullback_iff`). The key input is that a base
changed point meets the zero section exactly over the points where the original point does
(`EllipticCurveGeom.pointsPullback_left_apply_eq_zero_iff`), and over a field a point is zero
exactly when it meets the zero section (`EllipticCurveGeom.eq_one_iff_left_apply_eq_zero`).

For a finite group `A` and a homomorphism `u : A →* E(H)` to the points of `E` with values in a
scheme `H` over `S`, the points of `H` at which `u` is injective on the fibre form an open subset,
the **naive locus** of `u` (`EllipticCurveGeom.naiveLocus`), since the zero section has closed
image. When `u` is universal among homomorphisms from `A`, as the universal pair of points of
`E[N]` is for `A = (ℤ/Nℤ)²`, the naive locus represents the naive `A`-structures.

The group law on points of `E` is written multiplicatively, following `EllipticCurveGeom.mulBy`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective E φ`: the homomorphism
  `φ : A →* E(S)` is injective on every fibre of `E` over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveLocus u`: the points of `H` at which
  `u : A →* E(H)` is injective on the fibre; `naiveLocusOpens u` and `naiveLocusOver u` are the
  corresponding open subscheme of `H` and scheme over `S`, for finite `A`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiberwiseInjective_iff_injective`: over a field,
  injectivity on fibres is injectivity.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.pointsPullback`: injectivity
  on fibres is stable under base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.eq_of_comp_left_eq`: points
  in the image of a homomorphism injective on every fibre are distinguished by every field-valued
  point of the base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.left_apply_injective` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.disjoint_range`: distinct
  indices give distinct points in each fibre and disjoint section images.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiberwiseInjective_iff_forall_residueField`:
  injectivity on fibres is injectivity on the fibre over every residue field.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOpen_naiveLocus`: for finite `A`, the naive locus
  is open, and `range_left_subset_naiveLocus_iff` characterises the points landing in it.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiberwiseInjective_zmod_iff`: the naive
  `[Γ₁(N)]` condition, as `kP` missing the zero section for `0 < k < N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiberwiseInjective_zmod_prod_iff`: the naive
  `[Γ(N)]` condition, as `aP + bQ` missing the zero section for `(a, b) ≠ 0`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiberwiseInjective_iff_range_eq_ker`: over a
  separably closed field in which `N` is invertible, the naive `[Γ(N)]`-structures are the bases of
  `E[N](K)`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.existsUnique_eq_comp`:
  there, `GL₂(ℤ/Nℤ)` acts simply transitively on the naive `[Γ(N)]`-structures.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 (naive level structures
  where `N` is invertible) and 2.3.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

/-! ### Homomorphisms injective on every fibre -/

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {A : Type*} [Group A]

/-- A homomorphism `φ : A →* E(S)` from a group `A` to the group of `S`-points of an elliptic curve
`E` over `S` is **injective on every fibre** when, for every `a ≠ 1`, the section `φ a` of `E`
misses the zero section at every point of `S`: equivalently, `φ` followed by restriction to the
fibre of `E` over every field-valued point of `S` is injective
(`isFiberwiseInjective_iff_forall_residueField`, `IsFiberwiseInjective.injective_pointsPullback`).

For `A = ℤ/Nℤ` and `A = (ℤ/Nℤ)²`, over a base on which `N` is invertible, these are the naive
`[Γ₁(N)]`- and `[Γ(N)]`-structures on `E`. -/
def IsFiberwiseInjective (φ : A →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) : Prop :=
  ∀ (a : A) (s : S), (φ a).left s = E.zero s → a = 1

variable {E} {φ : A →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}

/-- A homomorphism is injective on every fibre exactly when the image of every `a ≠ 1` misses the
zero section everywhere. -/
theorem isFiberwiseInjective_iff :
    E.IsFiberwiseInjective φ ↔ ∀ a, a ≠ 1 → ∀ s : S, (φ a).left s ≠ E.zero s :=
  ⟨fun h a ha s hs ↦ ha (h a s hs), fun h a s hs ↦ by_contra fun ha ↦ h a ha s hs⟩

/-- **Injectivity on fibres is stable under base change.** -/
theorem IsFiberwiseInjective.pointsPullback {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
    {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (h : E.IsFiberwiseInjective φ) : E'.IsFiberwiseInjective ((pointsPullback hg h0).comp φ) :=
  fun a s' ha ↦ h a (f s') ((pointsPullback_left_apply_eq_zero_iff hg h0 _ s').mp ha)

/-- **Injectivity on fibres descends along surjective base changes.** -/
theorem isFiberwiseInjective_pointsPullback_iff {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
    {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (hf : Function.Surjective f) :
    E'.IsFiberwiseInjective ((pointsPullback hg h0).comp φ) ↔ E.IsFiberwiseInjective φ := by
  refine ⟨fun h a s hs ↦ ?_, fun h ↦ h.pointsPullback hg h0⟩
  obtain ⟨s', rfl⟩ := hf s
  exact h a s' ((pointsPullback_left_apply_eq_zero_iff hg h0 _ s').mpr hs)

/-- Restricting a homomorphism injective on every fibre along an injective homomorphism gives a
homomorphism injective on every fibre. -/
theorem IsFiberwiseInjective.comp {A' : Type*} [Group A'] (h : E.IsFiberwiseInjective φ)
    {ψ : A' →* A} (hψ : Function.Injective ψ) : E.IsFiberwiseInjective (φ.comp ψ) :=
  fun a s ha ↦ hψ ((h (ψ a) s ha).trans (map_one ψ).symm)

/-- Over a nonempty base, a homomorphism injective on every fibre is injective. -/
theorem IsFiberwiseInjective.injective [Nonempty S] (h : E.IsFiberwiseInjective φ) :
    Function.Injective φ := by
  obtain ⟨s⟩ := ‹Nonempty S›
  refine (injective_iff_map_eq_one φ).mpr fun a ha ↦ h a s ?_
  simp [ha]

/-! ### The naive locus -/

section NaiveLocus

variable {H : Over S} (u : A →* (H ⟶ Over.mk E.structureMap))

/-- **The naive locus of a family of homomorphisms.** For an elliptic curve `E` over a scheme `S`, a
scheme `H` over `S` and a homomorphism `u : A →* E(H)` to the group of points of `E` with values in
`H`, the set of points `h` of `H` at which `u` is injective on the fibre: for every `a ≠ 1`, the
point `u a` misses the zero section of `E` at `h`. -/
def naiveLocus : Set H.left :=
  {h | ∀ a, a ≠ 1 → (u a).left h ≠ E.zero (H.hom h)}

/-- The defining condition of the naive locus. -/
@[simp]
theorem mem_naiveLocus_iff {h : H.left} :
    h ∈ naiveLocus u ↔ ∀ a, a ≠ 1 → (u a).left h ≠ E.zero (H.hom h) :=
  Iff.rfl

/-- For a finite group `A`, the naive locus is open: it is the complement of the finitely many
closed sets where some `u a` with `a ≠ 1` meets the closed image of the zero section. -/
theorem isOpen_naiveLocus [Finite A] : IsOpen (naiveLocus u) := by
  have := E.zero.isClosedImmersion_of_comp_eq_id E.zero_comp_structureMap
  have h : naiveLocus u = ⋂ a ∈ {a : A | a ≠ 1}, ((u a).left ⁻¹' Set.range E.zero)ᶜ := by
    ext h
    simp only [naiveLocus, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
    exact forall₂_congr fun a _ ↦ (left_apply_mem_range_zero_iff (u a) h).not.symm
  rw [h]
  exact (Set.toFinite _).isOpen_biInter fun a _ ↦
    (E.zero.isClosedEmbedding.isClosed_range.preimage (u a).left.continuous).isOpen_compl

/-- A point `x` of `H` with values in a scheme `T` over `S` lands in the naive locus of `u` exactly
when, for every `a ≠ 1`, the point `x ≫ u a` of `E` misses the zero section at every point
of `T`. -/
theorem range_left_subset_naiveLocus_iff {T : Over S} (x : T ⟶ H) :
    Set.range x.left ⊆ naiveLocus u ↔
      ∀ a, a ≠ 1 → ∀ t, (x ≫ u a).left t ≠ E.zero (T.hom t) := by
  have hx (t : T.left) : H.hom (x.left t) = T.hom t := by
    rw [← Scheme.Hom.comp_apply, Over.w x]
  simp only [Set.range_subset_iff, mem_naiveLocus_iff, Over.comp_left, Scheme.Hom.comp_apply, hx]
  exact ⟨fun h a ha t ↦ h t a ha, fun h t a ha ↦ h a ha t⟩

/-- The naive locus of `u`, for a finite group `A`, as an open subscheme of `H`. -/
def naiveLocusOpens [Finite A] : H.left.Opens :=
  ⟨naiveLocus u, isOpen_naiveLocus u⟩

@[simp]
theorem coe_naiveLocusOpens [Finite A] : (naiveLocusOpens u : Set H.left) = naiveLocus u :=
  (rfl)

/-- The naive locus of `u`, for a finite group `A`, as a scheme over `S`. -/
noncomputable abbrev naiveLocusOver [Finite A] : Over S :=
  Over.mk ((naiveLocusOpens u).ι ≫ H.hom)

/-- The inclusion of the naive locus of `u` into `H`, an open immersion. -/
noncomputable def naiveLocusι [Finite A] : naiveLocusOver u ⟶ H :=
  Over.homMk (naiveLocusOpens u).ι rfl

@[simp]
theorem naiveLocusι_left [Finite A] : (naiveLocusι u).left = (naiveLocusOpens u).ι :=
  (rfl)

instance [Finite A] : IsOpenImmersion (naiveLocusι u).left :=
  inferInstanceAs (IsOpenImmersion (naiveLocusOpens u).ι)

instance [Finite A] : Mono (naiveLocusι u) :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono (naiveLocusOpens u).ι))

/-- The naive locus of `u` has, over `S`, every property of morphisms of schemes which is stable
under composition, holds for open immersions and holds for `H`. -/
theorem naiveLocusOver_hom_mem [Finite A] {W : MorphismProperty Scheme.{u}}
    [W.IsStableUnderComposition] (hW : @IsOpenImmersion ≤ W) (h : W H.hom) :
    W (naiveLocusOver u).hom :=
  W.comp_mem _ _ (hW _ inferInstance) h

end NaiveLocus

/-! ### Over a field -/

section Field

variable {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K)))

/-- **Over a field, injectivity on fibres is injectivity.** -/
theorem isFiberwiseInjective_iff_injective
    (φ : A →* (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)) :
    E.IsFiberwiseInjective φ ↔ Function.Injective φ := by
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  rw [injective_iff_map_eq_one]
  exact ⟨fun h a ha ↦ h a p ((E.eq_one_iff_left_apply_eq_zero _ p).mp ha),
    fun h a s hs ↦ h a ((E.eq_one_iff_left_apply_eq_zero _ s).mpr hs)⟩

end Field

/-- **Injectivity on the fibre over a field-valued point.** If `φ : A →* E(S)` is injective on
every fibre, then for every point `t` of `S` with values in a field `K`, in particular every
geometric point, `φ` followed by restriction to the fibre of `E` over `t` is injective. -/
theorem IsFiberwiseInjective.injective_pointsPullback (h : E.IsFiberwiseInjective φ)
    {K : Type u} [Field K] {E' : EllipticCurveGeom (Spec (.of K))} {g : E'.carrier ⟶ E.carrier}
    {t : Spec (.of K) ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap t)
    (h0 : E'.zero ≫ g = t ≫ E.zero) :
    Function.Injective ((EllipticCurveGeom.pointsPullback hg h0).comp φ) :=
  (E'.isFiberwiseInjective_iff_injective _).mp (h.pointsPullback hg h0)

/-- **Points of a fibrewise injective homomorphism are distinguished on field points.** If
`φ : A →* E(S)` is injective on every fibre and `φ c₁`, `φ c₂` agree after composition with a
point `t : Spec K ⟶ S` with values in a field, then `c₁ = c₂`. -/
theorem IsFiberwiseInjective.eq_of_comp_left_eq (hφ : E.IsFiberwiseInjective φ) {K : Type u}
    [Field K] (t : Spec (.of K) ⟶ S) {c₁ c₂ : A}
    (h : t ≫ (φ c₁).left = t ≫ (φ c₂).left) : c₁ = c₂ :=
  hφ.injective_pointsPullback (E.isPullback_baseChange t) (by simp)
    ((eq_pointsPullback_iff _ _).mpr (by rw [MonoidHom.comp_apply, pointsPullback_left_comp, h]))

/-- The underlying points of a fibrewise injective family of sections are distinct over each
point of the base. -/
theorem IsFiberwiseInjective.left_apply_injective (h : E.IsFiberwiseInjective φ) (s : S) :
    Function.Injective (fun a ↦ (φ a).left s) := by
  intro a b hab
  obtain ⟨p⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
  have hp : S.fromSpecResidueField s p = s := Scheme.fromSpecResidueField_apply s p
  refine h.eq_of_comp_left_eq (S.fromSpecResidueField s) ?_
  exact (comp_eq_comp_iff_of_section (left_comp_structureMap _) (left_comp_structureMap _) _ p).mpr
    ((congrArg (φ a).left hp).trans (hab.trans (congrArg (φ b).left hp).symm))

/-- Distinct sections of a fibrewise injective family have disjoint images. -/
theorem IsFiberwiseInjective.disjoint_range (h : E.IsFiberwiseInjective φ) {a b : A}
    (hab : a ≠ b) : Disjoint (Set.range (φ a).left) (Set.range (φ b).left) := by
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨s, rfl⟩ ⟨t, ht⟩
  have hs : t = s := by
    simpa [← Scheme.Hom.comp_apply] using congrArg E.structureMap ht
  subst t
  exact hab (h.left_apply_injective s ht.symm)

/-- **Injectivity on fibres is checked on residue fields.** A homomorphism `φ : A →* E(S)` is
injective on every fibre exactly when, for every point `s` of `S`, `φ` followed by restriction to
the fibre `E_{κ(s)}` of `E` over the residue field `κ(s)` is injective. -/
theorem isFiberwiseInjective_iff_forall_residueField :
    E.IsFiberwiseInjective φ ↔ ∀ s : S, Function.Injective
      ((pointsPullback (E.isPullback_baseChange (S.fromSpecResidueField s)) (by simp)).comp φ) := by
  refine ⟨fun h s ↦ h.injective_pointsPullback _ _, fun h a s hs ↦ ?_⟩
  obtain ⟨p⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
  rw [← Scheme.fromSpecResidueField_apply s p] at hs
  exact (injective_iff_map_eq_one _).mp (h s) a ((eq_one_iff_left_apply_eq_zero _ _ p).mpr
    ((pointsPullback_left_apply_eq_zero_iff _ _ _ p).mpr hs))

/-! ### Naive `[Γ₁(N)]`-structures -/

/-- **The naive `[Γ₁(N)]` condition.** A homomorphism `φ : ℤ/Nℤ →* E(S)`, given by the `S`-point
`P = φ 1` of `E[N]`, is injective on every fibre exactly when none of `P, 2P, …, (N - 1)P` meets
the zero section: `P` has exact order `N` in every fibre. -/
theorem isFiberwiseInjective_zmod_iff {N : ℕ} [NeZero N]
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsFiberwiseInjective φ ↔
      ∀ k : ℕ, 0 < k → k < N → ∀ s, (φ (.ofAdd 1) ^ k).left s ≠ E.zero s := by
  -- every element of `ℤ/Nℤ` is `k • 1` for a unique `k < N`
  have hφ (k : ℕ) : φ (.ofAdd 1) ^ k = φ (.ofAdd (k : ZMod N)) := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one]
  rw [isFiberwiseInjective_iff]
  refine ⟨fun h k hk hkN ↦ hφ k ▸ h _ fun h1 ↦ ?_, fun h a ha ↦ ?_⟩
  · rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.natCast_eq_zero_iff] at h1
    exact (Nat.not_dvd_of_pos_of_lt hk hkN) h1
  · have hval : a.toAdd.val ≠ 0 := by
      rwa [Ne, ZMod.val_eq_zero, ← ofAdd_eq_one, ofAdd_toAdd]
    have := h a.toAdd.val (Nat.pos_of_ne_zero hval) (ZMod.val_lt _)
    rwa [hφ, ZMod.natCast_zmod_val, ofAdd_toAdd] at this

/-! ### Naive `[Γ(N)]`-structures -/

/-- **The naive `[Γ(N)]` condition.** A homomorphism `φ : (ℤ/Nℤ)² →* E(S)`, given by the pair of
`S`-points `P = φ (1, 0)` and `Q = φ (0, 1)` of `E[N]`, is injective on every fibre exactly when no
combination `aP + bQ` with `(a, b) ≠ 0` in `(ℤ/Nℤ)²` meets the zero section. -/
theorem isFiberwiseInjective_zmod_prod_iff {N : ℕ} [NeZero N]
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsFiberwiseInjective φ ↔ ∀ a b : ZMod N, (a, b) ≠ 0 → ∀ s,
      (φ (.ofAdd (1, 0)) ^ a.val * φ (.ofAdd (0, 1)) ^ b.val).left s ≠ E.zero s := by
  -- `(a, b)` is `a.val • (1, 0) + b.val • (0, 1)`
  have hφ (a b : ZMod N) :
      φ (.ofAdd (1, 0)) ^ a.val * φ (.ofAdd (0, 1)) ^ b.val = φ (.ofAdd (a, b)) := by
    rw [← map_pow φ, ← map_pow φ, ← map_mul φ, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
    simp
  simp only [hφ, isFiberwiseInjective_iff, ne_eq, ← ofAdd_eq_one]
  exact ⟨fun h a b ↦ h _, fun h z ↦ h z.toAdd.1 z.toAdd.2⟩

/-! ### Naive `[Γ(N)]`-structures over a separably closed field -/

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] (E : EllipticCurveGeom (Spec (.of K))) {N : ℕ}

/-- **Naive `[Γ(N)]`-structures over a separably closed field are bases of `E[N]`.** Over a
separably closed field `K` in which `N` is invertible, a homomorphism `φ : (ℤ/Nℤ)² →* E(K)` is
injective on fibres exactly when its image is the `N`-torsion `E[N](K)`, that is, when it
identifies `(ℤ/Nℤ)²` with `E[N](K)`. -/
theorem isFiberwiseInjective_iff_range_eq_ker (hN : (N : K) ≠ 0)
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)) :
    E.IsFiberwiseInjective φ ↔ φ.range = (IsMonHom.monoidHom (E.mulBy N) _).ker := by
  have : NeZero N := ⟨by rintro rfl; exact hN Nat.cast_zero⟩
  -- `φ` takes values in `E[N](K)`, which has `N²` elements, as many as `(ℤ/Nℤ)²`
  have hle : φ.range ≤ (IsMonHom.monoidHom (E.mulBy N) _).ker := by
    rintro _ ⟨a, rfl⟩
    have ha : a ^ N = 1 := Multiplicative.toAdd.injective <| by
      ext <;> simp [nsmul_eq_mul]
    rw [MonoidHom.mem_ker, IsMonHom.monoidHom_apply, comp_mulBy, zpow_natCast, ← map_pow, ha,
      map_one]
  have hker : Nat.card (IsMonHom.monoidHom (E.mulBy N) (𝟙_ (Over (Spec (.of K))))).ker = N ^ 2 := by
    rw [← Nat.card_congr (E.torsionPointsMulEquiv N _).toEquiv,
      E.natCard_torsion (n := N) (by exact_mod_cast hN), Int.natAbs_natCast]
  have hA : Nat.card (Multiplicative (ZMod N × ZMod N)) = N ^ 2 := by
    simp [sq]
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hA] at hcard
  have : Finite (IsMonHom.monoidHom (E.mulBy N) (𝟙_ (Over (Spec (.of K))))).ker :=
    Nat.finite_of_card_ne_zero (by rw [hker]; exact pow_ne_zero 2 (NeZero.ne N))
  rw [isFiberwiseInjective_iff_injective, ← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  refine ⟨fun h ↦ Subgroup.eq_of_le_of_card_ge hle ?_, fun h ↦ ?_⟩
  · rw [h, Nat.one_mul] at hcard
    rw [hker, hcard]
  · rw [h, hker] at hcard
    exact (Nat.mul_eq_right (pow_ne_zero 2 (NeZero.ne N))).mp hcard

/-- **Every elliptic curve over a separably closed field has a naive `[Γ(N)]`-structure** when
`N` is invertible in the field: there is a homomorphism `(ℤ/Nℤ)² →* E(K)` injective on fibres. -/
theorem exists_isFiberwiseInjective (hN : (N : K) ≠ 0) :
    ∃ φ : Multiplicative (ZMod N × ZMod N) →*
      (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap), E.IsFiberwiseInjective φ := by
  have : NeZero N := ⟨by rintro rfl; exact hN Nat.cast_zero⟩
  -- `E` is the curve of a Weierstrass equation `W`, whose `N`-torsion points form `(ℤ/Nℤ)²`
  obtain ⟨W, _, e, he, h0⟩ := E.exists_iso_toEllipticCurveGeom
  obtain ⟨eW⟩ := W.nonempty_toEllipticCurveGeom_torsion_mulEquiv_prod N hN
  let φW := (Subgroup.subtype _).comp
    ((W.toEllipticCurveGeom.torsionPointsMulEquiv N _).toMonoidHom.comp eW.symm.toMonoidHom)
  have hφW : W.toEllipticCurveGeom.IsFiberwiseInjective φW :=
    (isFiberwiseInjective_iff_injective _ _).mpr <|
      Subtype.val_injective.comp ((MulEquiv.injective _).comp eW.symm.injective)
  -- transport along the isomorphism `e`, a pullback square over the identity of `Spec K`
  have hg : IsPullback e.inv E.structureMap W.toEllipticCurveGeom.structureMap (𝟙 _) :=
    .of_horiz_isIso ⟨by simp [Iso.inv_comp_eq, he]⟩
  exact ⟨_, hφW.pointsPullback hg (by simp [← h0])⟩

/-- **`GL₂(ℤ/Nℤ)` acts simply transitively on the naive `[Γ(N)]`-structures over a separably
closed field.** If `N` is invertible in `K`, then any two homomorphisms
`φ ψ : (ℤ/Nℤ)² →* E(K)` injective on fibres differ by a unique invertible matrix `g` acting on
`(ℤ/Nℤ)²`: `ψ = φ ∘ g`. Both are isomorphisms onto `E[N](K)`, and `g` is the matrix of
`φ⁻¹ ∘ ψ`. -/
theorem IsFiberwiseInjective.existsUnique_eq_comp (hN : (N : K) ≠ 0)
    {φ ψ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)}
    (hφ : E.IsFiberwiseInjective φ) (hψ : E.IsFiberwiseInjective ψ) :
    ∃! g : GL (Fin 2) (ZMod N), ψ = φ.comp (zmodProdMulAutEquiv N g).toMonoidHom := by
  have hφi := (isFiberwiseInjective_iff_injective E φ).mp hφ
  have hψi := (isFiberwiseInjective_iff_injective E ψ).mp hψ
  -- `φ` and `ψ` are isomorphisms onto the same subgroup `E[N](K)`
  have hrange : ψ.range = φ.range := by
    rw [(isFiberwiseInjective_iff_range_eq_ker E hN ψ).mp hψ,
      (isFiberwiseInjective_iff_range_eq_ker E hN φ).mp hφ]
  let σ := (MonoidHom.ofInjective hψi).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hφi).symm)
  have hσ : ψ = φ.comp σ.toMonoidHom := MonoidHom.ext fun a ↦ by
    simp [σ, MonoidHom.apply_ofInjective_symm, MonoidHom.ofInjective_apply]
  refine ⟨(zmodProdMulAutEquiv N).symm σ, by simpa using hσ, fun g hg ↦ ?_⟩
  rw [MulEquiv.eq_symm_apply]
  refine MulEquiv.ext fun a ↦ hφi ?_
  simpa using (DFunLike.congr_fun hg a).symm.trans (DFunLike.congr_fun hσ a)

end SepClosed

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
