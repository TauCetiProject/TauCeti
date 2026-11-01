/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cochain

/-!
# The cup pairing on the total coinduced resolution

The Alexander–Whitney pairings in individual degrees extend bilinearly to the direct sums of
the shifted coinduced resolutions. This gives a pairing on single carriers, suitable for applying
tensor induction: its diagonal tensors can be compared with products of diagonal tensors.

`TauCeti.TopPairing.gradedResolutionCupPairing` preserves total degree, is equivariant, and
agrees with the canonical homogeneous-cochain cup under inclusion into the total resolution.
Its differential satisfies the signed Leibniz rule on homogeneous elements. When the target
coefficients have exponent two, the sign disappears and the unsigned rule holds for all
elements of the total resolution. In particular, products of invariant homogeneous cocycles
are invariant homogeneous cocycles.

The construction extends `TauCeti.TopPairing.resolutionCupPairing` using the universal property
of direct sums; it does not choose a different cochain product.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter V, §3, for the Alexander–Whitney product.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §§2–6, for tensor induction and multiplicativity.
-/

public section

namespace TauCeti.TopPairing

open CategoryTheory
open scoped DirectSum

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-- The Alexander–Whitney pairing extended bilinearly to the total shifted resolutions. -/
noncomputable def gradedResolutionCupPairing :
    X.gradedResolutionModule →ₗ[R] Y.gradedResolutionModule →ₗ[R]
      Z.gradedResolutionModule :=
  DirectSum.toModule R ℕ _ fun m ↦
    (DFinsupp.lsum R (R := R) (M := fun n : ℕ ↦ (TopRep.resolutionX Y (n + 1)).V)
      (N := Z.gradedResolutionModule)).toLinearMap.comp (LinearMap.pi fun n ↦
      (P.resolutionCupPairing m n).compr₂
        (DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Z (k + 1)).V) (m + n)))

/-- On two summands the total cup is the original degreewise cup, included in the sum degree. -/
@[simp]
theorem gradedResolutionCupPairing_lof (m n : ℕ)
    (a : (TopRep.resolutionX X (m + 1)).V)
    (b : (TopRep.resolutionX Y (n + 1)).V) :
    P.gradedResolutionCupPairing
        (DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX X (k + 1)).V) m a)
        (DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Y (k + 1)).V) n b) =
      DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Z (k + 1)).V) (m + n)
        (P.resolutionCupPairing m n a b) := by
  rw [gradedResolutionCupPairing, DirectSum.toModule_lof]
  exact DFinsupp.lsum_single (S := R)
    (M := fun n : ℕ ↦ (TopRep.resolutionX Y (n + 1)).V)
    (fun n ↦ ((P.resolutionCupPairing m n).compr₂
      (DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Z (k + 1)).V) (m + n))) a) n b

/-- The cup of elements of degrees `m` and `n` has degree `m + n`. -/
theorem gradedResolutionCupPairing_mem {m n : ℕ}
    {a : X.gradedResolutionModule} {b : Y.gradedResolutionModule}
    (ha : a ∈ X.gradedResolutionPiece m) (hb : b ∈ Y.gradedResolutionPiece n) :
    P.gradedResolutionCupPairing a b ∈ Z.gradedResolutionPiece (m + n : ℕ) := by
  rw [TopRep.gradedResolutionPiece_natCast] at ha hb ⊢
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨_, (P.gradedResolutionCupPairing_lof m n a b).symm⟩

/-- The group acts diagonally on the total cup pairing. -/
theorem gradedResolutionCupPairing_ρ (g : G)
    (a : X.gradedResolutionModule) (b : Y.gradedResolutionModule) :
    P.gradedResolutionCupPairing (X.gradedResolutionRepresentation g a)
        (Y.gradedResolutionRepresentation g b) =
      Z.gradedResolutionRepresentation g (P.gradedResolutionCupPairing a b) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m a =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n b =>
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R,
        X.gradedResolutionRepresentation_lof m g a,
        Y.gradedResolutionRepresentation_lof n g b,
        P.gradedResolutionCupPairing_lof, P.gradedResolutionCupPairing_lof,
        Z.gradedResolutionRepresentation_lof]
      exact congrArg _ (P.resolutionCupPairing_ρ m n g a b)
    | add b b' hb hb' => simp only [map_add, hb, hb']
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']

/-- Inclusion of homogeneous cochains carries their cup to the total cup. -/
theorem gradedResolutionCupPairing_cochainToGradedResolution (m n : ℕ)
    (a : (TopRep.homogeneousCochains X).X m)
    (b : (TopRep.homogeneousCochains Y).X n) :
    P.gradedResolutionCupPairing (X.cochainToGradedResolution m a)
        (Y.cochainToGradedResolution n b) =
      Z.cochainToGradedResolution (m + n) (P.cupCochain m n a b) := by
  rw [TopRep.cochainToGradedResolution_apply, TopRep.cochainToGradedResolution_apply,
    TopRep.cochainToGradedResolution_apply, gradedResolutionCupPairing_lof, coe_cupCochain]

/-- The cup pairing on total resolutions extends the coefficient pairing along augmentation. -/
@[simp↓]
theorem gradedResolutionCupPairing_augmentation (a : X.V) (b : Y.V) :
    P.gradedResolutionCupPairing (X.gradedResolutionAugmentation a)
        (Y.gradedResolutionAugmentation b) =
      Z.gradedResolutionAugmentation (P.bil a b) := by
  rw [TopRep.gradedResolutionAugmentation_apply, TopRep.gradedResolutionAugmentation_apply,
    TopRep.gradedResolutionAugmentation_apply, gradedResolutionCupPairing_lof]
  congr 1
  apply ContinuousMap.ext
  intro g
  rw [resolutionCupPairing_zero_zero_apply]
  rfl

/-- The total cup pairing is natural in both the group and the coefficients. -/
theorem gradedResolutionCupPairing_gradedResolutionMap
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {X' Y' Z' : TopRep.{max v w} R H} (P' : TopPairing X' Y' Z') (φ : H →ₜ* G)
    (fX : TopRep.res (φ : H →* G) X ⟶ X') (fY : TopRep.res (φ : H →* G) Y ⟶ Y')
    (fZ : TopRep.res (φ : H →* G) Z ⟶ Z')
    (hpair : ∀ (x : X.V) (y : Y.V), fZ (P.bil x y) = P'.bil (fX x) (fY y))
    (a : X.gradedResolutionModule) (b : Y.gradedResolutionModule) :
    TopRep.gradedResolutionMap φ fZ (P.gradedResolutionCupPairing a b) =
      P'.gradedResolutionCupPairing (TopRep.gradedResolutionMap φ fX a)
        (TopRep.gradedResolutionMap φ fY b) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m a =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n b =>
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R,
        P.gradedResolutionCupPairing_lof, TopRep.gradedResolutionMap_lof,
        TopRep.gradedResolutionMap_lof φ fX m a, TopRep.gradedResolutionMap_lof φ fY n b,
        P'.gradedResolutionCupPairing_lof]
      exact congrArg _ (P.resolutionCupPairing_resolutionMap P' φ fX fY fZ hpair m n a b)
    | add b b' hb hb' => simp only [map_add, hb, hb']
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']

/-- The signed Leibniz rule for homogeneous elements of the total resolution. All three terms
live on the same carrier, so the statement needs no transport between equal degrees. -/
theorem gradedResolutionCupPairing_leibniz {m n : ℕ}
    {a : X.gradedResolutionModule} {b : Y.gradedResolutionModule}
    (ha : a ∈ X.gradedResolutionPiece m) (hb : b ∈ Y.gradedResolutionPiece n) :
    Z.gradedResolutionDifferential (P.gradedResolutionCupPairing a b) =
      P.gradedResolutionCupPairing (X.gradedResolutionDifferential a) b +
        (-1 : R) ^ m • P.gradedResolutionCupPairing a (Y.gradedResolutionDifferential b) := by
  rw [TopRep.gradedResolutionPiece_natCast] at ha hb
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  -- Inclusion in the direct sum absorbs the transport in the degreewise Leibniz rule.
  have ht (i j : ℕ) (h : i = j) (x : (TopRep.resolutionX Z (i + 1)).V) :
      DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Z (k + 1)).V) j
          (((TopRep.resolution Z).XIsoOfEq (congrArg Nat.succ h)).hom.hom x) =
        DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Z (k + 1)).V) i x := by
    subst j
    simp [ContIntertwiningMap.id_apply]
  have h := congrArg
    (DirectSum.lof R ℕ (fun k ↦ (TopRep.resolutionX Z (k + 1)).V) (m + n + 1))
    (P.resolutionCupPairing_leibniz m n a b)
  rw [map_add, map_smul, ht _ _ (by omega)] at h
  rw [P.gradedResolutionCupPairing_lof m n a b,
    X.gradedResolutionDifferential_lof m a, Y.gradedResolutionDifferential_lof n b,
    Z.gradedResolutionDifferential_lof, P.gradedResolutionCupPairing_lof,
    P.gradedResolutionCupPairing_lof]
  exact h

/-- Cups of homogeneous cocycles are cocycles on the total resolution. -/
theorem gradedResolutionDifferential_cup_eq_zero {m n : ℕ}
    {a : X.gradedResolutionModule} {b : Y.gradedResolutionModule}
    (ha : a ∈ X.gradedResolutionPiece m) (hb : b ∈ Y.gradedResolutionPiece n)
    (hda : X.gradedResolutionDifferential a = 0)
    (hdb : Y.gradedResolutionDifferential b = 0) :
    Z.gradedResolutionDifferential (P.gradedResolutionCupPairing a b) = 0 := by
  simp [P.gradedResolutionCupPairing_leibniz ha hb, hda, hdb]

/-- In exponent two the differential obeys the unsigned Leibniz rule, even on elements with
several homogeneous components. This is the rule used by tensor-induced resolutions. -/
theorem gradedResolutionCupPairing_leibniz_of_add_self_eq_zero
    (hZ : ∀ z : Z.V, z + z = 0)
    (a : X.gradedResolutionModule) (b : Y.gradedResolutionModule) :
    Z.gradedResolutionDifferential (P.gradedResolutionCupPairing a b) =
      P.gradedResolutionCupPairing (X.gradedResolutionDifferential a) b +
        P.gradedResolutionCupPairing a (Y.gradedResolutionDifferential b) := by
  have hsign (m : ℕ) (z : Z.gradedResolutionModule) : (-1 : R) ^ m • z = z := by
    have hz : -z = z := neg_eq_iff_add_eq_zero.mpr
      (TopRep.gradedResolutionModule_add_self_eq_zero Z hZ z)
    induction m with
    | zero => simp
    | succ m hm => rw [pow_succ, mul_smul, neg_one_smul, hz, hm]
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m a =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n b =>
      simpa only [hsign, DirectSum.lof_eq_of] using P.gradedResolutionCupPairing_leibniz
        (X.lof_mem_gradedResolutionPiece m a) (Y.lof_mem_gradedResolutionPiece n b)
    | add b b' hb hb' => simp only [map_add, hb, hb']; abel
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']; abel

end TauCeti.TopPairing
