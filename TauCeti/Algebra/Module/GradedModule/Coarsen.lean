/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.Algebra.DirectSum.Component
public import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.Algebra.DirectSum.Internal

/-!
# Coarsening a grading along a map of index types

A family of submodules `ℳ : ι → Submodule R M` and a map `f : ι → κ` of index types give a
family indexed by `κ`: its degree-`k` piece is the sum of the pieces `ℳ i` with `f i = k`.  When
`ℳ` is an internal direct-sum decomposition, so is the coarsened family, over any semiring
(`DirectSum.IsInternal.iSup_fiber`).

The main example is the parity grading of an integer grading, obtained by reducing degrees
modulo two: its even piece is the sum of the pieces of degree `2 * k`, and its odd piece is the
sum of the pieces of degree `2 * k + 1`.  This is how an integer-graded object is regarded as a
super (parity-graded) object, for example when Koszul signs only depend on parities.  Conversely,
every internal `ZMod 2`-grading lifts to an internal `ℤ`-grading concentrated in degrees `0` and
`1` (`TauCeti.InternalGrading.ofParity`), providing a right inverse to parity reduction, and carries
an involutive parity sign endomorphism (`TauCeti.InternalGrading.parityTwist`).

## Main definitions

* `TauCeti.coarsenGrading ℳ f`: the coarsening of a family of submodules along `f : ι → κ`.
* `TauCeti.parityGrading ℳ`: the parity grading of an integer-indexed family of submodules.
* `TauCeti.InternalGrading.coarsen` and `TauCeti.InternalGrading.parity`: the same constructions
  for bundled internal gradings.
* `TauCeti.InternalGrading.ofParity`: the canonical integer lift of an internal `ZMod 2`-grading,
  concentrated in degrees `0` and `1`.
* `TauCeti.InternalGrading.parityTwist`: the parity involution fixing the even piece and negating
  the odd piece.

## Main results

* `TauCeti.coarsenGrading_le_iff`: the universal property of the coarsened pieces, and
  `TauCeti.coarsenGrading_induction`: the corresponding induction principle on elements.
* `TauCeti.decompose_coarsenGrading`: the coarsened homogeneous components are the sums of the
  original components in each fibre.
* `TauCeti.mem_coarsenGrading_iff`: an element lies in the coarsened piece of degree `k` exactly
  when its components outside the fibre over `k` vanish.
* `TauCeti.LinearMap.IsHomogeneous.coarsenGrading`: a homogeneous linear map of degree `q` is
  homogeneous of degree `f q` for gradings coarsened along an additive homomorphism `f`.
* `TauCeti.parityGrading_zero` and `TauCeti.parityGrading_one`: the even and odd pieces.
* `TauCeti.InternalGrading.parity_ofParity`: `ofParity` is a right inverse to `parity`.
* `TauCeti.InternalGrading.parityTwist_apply_of_mem`,
  `TauCeti.InternalGrading.isHomogeneous_parityTwist`, and
  `TauCeti.InternalGrading.parityTwist_ofDecomposition_mul`: action, degree preservation, and
  multiplicativity of the parity involution.
-/

public section

open DirectSum

namespace TauCeti

universe uR uM uι uκ

variable {R : Type uR} {M : Type uM} {ι : Type uι} {κ : Type uκ}
  [Semiring R] [AddCommMonoid M] [Module R M]

section Coarsen

/-- The coarsening of a family of submodules `ℳ : ι → Submodule R M` along a map `f : ι → κ` of
index types: the degree-`k` piece is the sum of the pieces `ℳ i` over the fibre `f i = k`. -/
def coarsenGrading (ℳ : ι → Submodule R M) (f : ι → κ) (k : κ) : Submodule R M :=
  ⨆ (i) (_ : f i = k), ℳ i

theorem coarsenGrading_apply (ℳ : ι → Submodule R M) (f : ι → κ) (k : κ) :
    coarsenGrading ℳ f k = ⨆ (i) (_ : f i = k), ℳ i := (rfl)

/-- The universal property of the coarsened pieces: the degree-`k` piece lies in a submodule
exactly when every piece in the fibre over `k` does. -/
theorem coarsenGrading_le_iff {ℳ : ι → Submodule R M} {f : ι → κ} {k : κ} {N : Submodule R M} :
    coarsenGrading ℳ f k ≤ N ↔ ∀ i, f i = k → ℳ i ≤ N :=
  iSup₂_le_iff

/-- Each piece is contained in the coarsened piece of the image degree. -/
theorem le_coarsenGrading (ℳ : ι → Submodule R M) (f : ι → κ) (i : ι) :
    ℳ i ≤ coarsenGrading ℳ f (f i) :=
  le_iSup₂_of_le i rfl le_rfl

/-- An element of degree `i` has degree `f i` in the coarsened grading. -/
theorem mem_coarsenGrading_of_mem {ℳ : ι → Submodule R M} (f : ι → κ) {i : ι} {x : M}
    (hx : x ∈ ℳ i) : x ∈ coarsenGrading ℳ f (f i) :=
  le_coarsenGrading ℳ f i hx

/-- Induction on membership in a coarsened piece: a property that holds on every piece of the
fibre over `k` and is closed under zero and addition holds on the coarsened piece of degree `k`. -/
@[elab_as_elim]
theorem coarsenGrading_induction {ℳ : ι → Submodule R M} {f : ι → κ} {k : κ}
    {motive : M → Prop} {x : M} (hx : x ∈ coarsenGrading ℳ f k)
    (mem : ∀ i, f i = k → ∀ y ∈ ℳ i, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x :=
  Submodule.iSup_induction (motive := motive) _ hx
    (fun i _ hy ↦ Submodule.iSup_induction (motive := motive) _ hy (fun hi z hz ↦ mem i hi z hz)
      zero add) zero add

/-- Coarsening along the identity does nothing. -/
@[simp]
theorem coarsenGrading_id (ℳ : ι → Submodule R M) : coarsenGrading ℳ id = ℳ := by
  funext k
  exact le_antisymm (coarsenGrading_le_iff.2 fun _ h ↦ h ▸ le_rfl) (le_coarsenGrading ℳ id k)

/-- Coarsening twice is coarsening along the composite. -/
@[simp]
theorem coarsenGrading_coarsenGrading {ν : Type*} (ℳ : ι → Submodule R M) (f : ι → κ)
    (g : κ → ν) : coarsenGrading (coarsenGrading ℳ f) g = coarsenGrading ℳ (g ∘ f) := by
  funext n
  refine le_antisymm (coarsenGrading_le_iff.2 fun k hk ↦ coarsenGrading_le_iff.2 fun i hi ↦ ?_)
    (coarsenGrading_le_iff.2 fun i hi ↦ ?_)
  · exact le_coarsenGrading ℳ (g ∘ f) i |>.trans_eq (by rw [Function.comp_apply, hi, hk])
  · exact (le_coarsenGrading ℳ f i).trans
      (le_coarsenGrading (coarsenGrading ℳ f) g (f i) |>.trans_eq (by rw [← hi]; rfl))

variable [DecidableEq ι] [DecidableEq κ]

/-- The decomposition into coarsened pieces, chosen from the internality of the coarsened family
(`DirectSum.IsInternal.iSup_fiber`); any two decompositions of the same family agree. -/
noncomputable instance (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : ι → κ) :
    Decomposition (coarsenGrading ℳ f) :=
  -- The internality proof is elaborated as a proof, where the body of `coarsenGrading` unfolds.
  IsInternal.chooseDecomposition _ (by exact IsInternal.iSup_fiber (Decomposition.isInternal ℳ) f)

variable (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : ι → κ)

/-- The coarsened homogeneous component of degree `k` is the sum of the components whose degree
lies in the fibre over `k`. -/
theorem decompose_coarsenGrading [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (x : M) (k : κ) :
    (decompose (coarsenGrading ℳ f) x k : M) =
      ∑ i ∈ (decompose ℳ x).support with f i = k, (decompose ℳ x i : M) := by
  conv_lhs => rw [← sum_support_decompose ℳ x]
  rw [decompose_sum, DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hx := mem_coarsenGrading_of_mem f (decompose ℳ x i).property
  split_ifs with hi
  · exact hi ▸ decompose_of_mem_same _ hx
  · exact decompose_of_mem_ne _ hx hi

omit [DecidableEq κ] in
/-- An element lies in the coarsened piece of degree `k` exactly when its homogeneous components
of every degree outside the fibre over `k` vanish. -/
theorem mem_coarsenGrading_iff {x : M} {k : κ} :
    x ∈ coarsenGrading ℳ f k ↔ ∀ i, f i ≠ k → (decompose ℳ x i : M) = 0 := by
  classical
  refine ⟨fun hx i hi ↦ ?_, fun hx ↦ ?_⟩
  · -- The `i`-th component vanishes on every piece of the fibre over `k`.
    let π : M →ₗ[R] ℳ i := (component R ι (fun i ↦ ℳ i) i).comp
      (decomposeLinearEquiv ℳ).toLinearMap
    have hle : coarsenGrading ℳ f k ≤ LinearMap.ker π :=
      coarsenGrading_le_iff.2 fun j hj y hy ↦ by
        rw [LinearMap.mem_ker, ← Subtype.coe_inj]
        exact decompose_of_mem_ne ℳ hy (by rintro rfl; exact hi hj)
    exact congrArg Subtype.val (LinearMap.mem_ker.1 (hle hx))
  · rw [← sum_support_decompose ℳ x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : f i = k
    · exact hi ▸ mem_coarsenGrading_of_mem f (decompose ℳ x i).property
    · rw [hx i hi]
      exact zero_mem _

end Coarsen

section Homogeneous

variable {N : Type*} [AddCommMonoid N] [Module R N] [AddMonoid ι] [AddMonoid κ]

/-- A linear map that is homogeneous of degree `q` for two gradings is homogeneous of degree
`f q` for the gradings coarsened along an additive homomorphism `f`. -/
theorem LinearMap.IsHomogeneous.coarsenGrading {g : M →ₗ[R] N} {ℳ : ι → Submodule R M}
    {𝒩 : ι → Submodule R N} {q : ι} (hg : LinearMap.IsHomogeneous g ℳ 𝒩 q) (f : ι →+ κ) :
    LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f) (f q) :=
  LinearMap.isHomogeneous_def.2 fun k x hx ↦ by
    have hle : TauCeti.coarsenGrading ℳ f k ≤
        (TauCeti.coarsenGrading 𝒩 f (k + f q)).comap g :=
      coarsenGrading_le_iff.2 fun i hi y hy ↦ by
        simpa [hi] using mem_coarsenGrading_of_mem f (hg.map_mem hy)
    exact hle hx

end Homogeneous

section Parity

/-- The parity grading of an integer-indexed family of submodules, indexed by `ZMod 2`: its
even piece is the sum of the pieces of even degree and its odd piece is the sum of the pieces
of odd degree (`parityGrading_zero`, `parityGrading_one`).  It is reducible to the coarsening
along reduction modulo two, so the `coarsenGrading` API and instances apply to it directly. -/
abbrev parityGrading (ℳ : ℤ → Submodule R M) : ZMod 2 → Submodule R M :=
  coarsenGrading ℳ (Int.castAddHom (ZMod 2))

/-- An element of degree `n` has parity `n` modulo two. -/
theorem mem_parityGrading_of_mem {ℳ : ℤ → Submodule R M} {n : ℤ} {x : M} (hx : x ∈ ℳ n) :
    x ∈ parityGrading ℳ n :=
  mem_coarsenGrading_of_mem (Int.castAddHom (ZMod 2)) hx

/-- The universal property of the parity pieces. -/
theorem parityGrading_le_iff {ℳ : ℤ → Submodule R M} {i : ZMod 2} {N : Submodule R M} :
    parityGrading ℳ i ≤ N ↔ ∀ n : ℤ, (n : ZMod 2) = i → ℳ n ≤ N :=
  coarsenGrading_le_iff

/-- The even piece of the parity grading is the sum of the pieces of degree `2 * k`. -/
theorem parityGrading_zero (ℳ : ℤ → Submodule R M) :
    parityGrading ℳ 0 = ⨆ k : ℤ, ℳ (2 * k) := by
  refine le_antisymm (parityGrading_le_iff.2 fun n hn ↦ ?_) (iSup_le fun k x hx ↦ ?_)
  · obtain ⟨k, rfl⟩ : 2 ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).1 hn
    exact le_iSup (fun k ↦ ℳ (2 * k)) k
  · simpa [CharP.ofNat_eq_zero] using mem_parityGrading_of_mem hx

/-- The odd piece of the parity grading is the sum of the pieces of degree `2 * k + 1`. -/
theorem parityGrading_one (ℳ : ℤ → Submodule R M) :
    parityGrading ℳ 1 = ⨆ k : ℤ, ℳ (2 * k + 1) := by
  refine le_antisymm (parityGrading_le_iff.2 fun n hn ↦ ?_) (iSup_le fun k x hx ↦ ?_)
  · obtain ⟨k, hk⟩ : 2 ∣ n - 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 (by push_cast; rw [hn, sub_self])
    rw [eq_add_of_sub_eq hk]
    exact le_iSup (fun k ↦ ℳ (2 * k + 1)) k
  · simpa [CharP.ofNat_eq_zero] using mem_parityGrading_of_mem hx

end Parity

namespace InternalGrading

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The coarsening of an internal grading along a map `f : ι → κ` of index types: the degree-`k`
piece is the sum of the pieces whose degree lies in the fibre over `k`. -/
noncomputable def coarsen (G : InternalGrading R M ι) (f : ι → κ) : InternalGrading R M κ where
  piece := coarsenGrading G.piece f
  isInternal := G.isInternal.iSup_fiber f

@[simp]
theorem coarsen_piece (G : InternalGrading R M ι) (f : ι → κ) :
    (G.coarsen f).piece = coarsenGrading G.piece f := (rfl)

/-- The parity grading of an internal integer grading: the internal `ZMod 2`-grading whose even
piece is the sum of the pieces of degree `2 * k` and whose odd piece is the sum of the pieces of
degree `2 * k + 1`. -/
noncomputable def parity (G : InternalGrading R M ℤ) : InternalGrading R M (ZMod 2) :=
  G.coarsen (Int.castAddHom (ZMod 2))

@[simp]
theorem parity_piece (G : InternalGrading R M ℤ) : G.parity.piece = parityGrading G.piece := (rfl)

/-- The canonical integer lift of an internal `ZMod 2`-grading, placing `G.piece 0` in degree `0`,
`G.piece 1` in degree `1`, and `⊥` in all other degrees. It is a right inverse to
`InternalGrading.parity` (`parity_ofParity`). -/
noncomputable def ofParity (G : InternalGrading R M (ZMod 2)) : InternalGrading R M ℤ :=
  G.coarsen fun i ↦ (i.val : ℤ)

/-- The pieces of `G.ofParity` are `G.piece 0` in degree `0`, `G.piece 1` in degree `1`, and `⊥`
elsewhere. -/
@[simp]
theorem ofParity_piece (G : InternalGrading R M (ZMod 2)) (p : ℤ) :
    G.ofParity.piece p = if p = 0 then G.piece 0 else if p = 1 then G.piece 1 else ⊥ := by
  rw [ofParity, coarsen_piece, coarsenGrading_apply]
  refine le_antisymm (iSup₂_le fun i hi ↦ ?_) ?_
  · match i with
    | 0 => subst hi; simp
    | 1 => subst hi; simp [ZMod.val_one]
  · by_cases h0 : p = 0
    · subst h0
      exact le_iSup₂_of_le (0 : ZMod 2) (by decide) (by simp)
    · by_cases h1 : p = 1
      · subst h1
        exact le_iSup₂_of_le (1 : ZMod 2) (by decide) (by simp)
      · simp [h0, h1]

/-- The degree-`0` piece of `G.ofParity` is the even piece `G.piece 0`. -/
theorem ofParity_piece_zero (G : InternalGrading R M (ZMod 2)) :
    G.ofParity.piece 0 = G.piece 0 := by
  simp

/-- The degree-`1` piece of `G.ofParity` is the odd piece `G.piece 1`. -/
theorem ofParity_piece_one (G : InternalGrading R M (ZMod 2)) :
    G.ofParity.piece 1 = G.piece 1 := by
  simp

/-- Outside degrees `0` and `1`, the pieces of `G.ofParity` are trivial. -/
theorem ofParity_piece_of_ne (G : InternalGrading R M (ZMod 2)) {p : ℤ}
    (h0 : p ≠ 0) (h1 : p ≠ 1) : G.ofParity.piece p = ⊥ := by
  simp [h0, h1]

/-- Lifting an internal `ZMod 2`-grading to `ℤ` in degrees `0` and `1` and reducing modulo two
recovers the original grading. -/
@[simp]
theorem parity_ofParity (G : InternalGrading R M (ZMod 2)) : G.ofParity.parity = G := by
  apply InternalGrading.ext
  have hcomp : (Int.castAddHom (ZMod 2) ∘ fun i : ZMod 2 ↦ (i.val : ℤ)) = id := by
    funext i
    simp
  have hpiece : G.ofParity.parity.piece = G.piece := by
    rw [parity_piece, ofParity, coarsen_piece, parityGrading, coarsenGrading_coarsenGrading,
      hcomp, coarsenGrading_id]
  exact congrFun hpiece

section ParityTwist

variable {R : Type uR} {M : Type uM} [Semiring R] [AddCommGroup M] [Module R M]

/-- The parity involution on an internally `ZMod 2`-graded module, fixing the even piece and
negating the odd piece (`parityTwist_apply_of_mem`). This is the `ZMod 2`-graded counterpart of
`InternalGrading.koszulTwist G 1`. -/
noncomputable def parityTwist (G : InternalGrading R M (ZMod 2)) : M →ₗ[R] M :=
  homogeneousComponent G.piece 0 - homogeneousComponent G.piece 1

/-- `parityTwist` is the difference of the even and odd homogeneous projections. -/
theorem parityTwist_apply (G : InternalGrading R M (ZMod 2)) (x : M) :
    G.parityTwist x = homogeneousComponent G.piece 0 x - homogeneousComponent G.piece 1 x :=
  (rfl)

/-- On an element of parity `i`, `parityTwist` acts as multiplication by `(-1) ^ i`. -/
theorem parityTwist_apply_of_mem (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) : G.parityTwist x = ((-1 : ℤˣ) ^ i) • x := by
  rw [parityTwist_apply]
  match i with
  | 0 =>
    rw [homogeneousComponent_apply_of_mem G.piece hx,
      homogeneousComponent_apply_of_mem_ne G.piece hx (by decide : (0 : ZMod 2) ≠ 1)]
    simp
  | 1 =>
    rw [homogeneousComponent_apply_of_mem_ne G.piece hx (by decide : (1 : ZMod 2) ≠ 0),
      homogeneousComponent_apply_of_mem G.piece hx]
    simp

/-- The parity involution preserves both parity pieces. -/
theorem parityTwist_mem_piece (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) : G.parityTwist x ∈ G.piece i := by
  -- Direct summands of an `AddCommGroup` are closed under negation even over a `Semiring`.
  have hneg : -x ∈ G.piece i := by
    have h : -x = homogeneousComponent G.piece i (-x) := by
      rw [map_neg, homogeneousComponent_apply_of_mem G.piece hx]
    exact h ▸ homogeneousComponent_mem G.piece i (-x)
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ i) with h | h <;>
    simp [G.parityTwist_apply_of_mem hx, h, hx, hneg]

/-- The parity involution is homogeneous of parity `0`. -/
theorem isHomogeneous_parityTwist (G : InternalGrading R M (ZMod 2)) :
    LinearMap.IsHomogeneous G.parityTwist G.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using G.parityTwist_mem_piece hx

/-- The parity involution squares to the identity. -/
@[simp]
theorem parityTwist_comp_self (G : InternalGrading R M (ZMod 2)) :
    G.parityTwist ∘ₗ G.parityTwist = LinearMap.id := by
  refine G.linearMap_ext fun i x hx ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [G.parityTwist_apply_of_mem (G.parityTwist_mem_piece hx), G.parityTwist_apply_of_mem hx,
    smul_smul, ← uzpow_add, CharTwo.add_self_eq_zero, uzpow_zero, one_smul]

/-- The parity involution is involutive pointwise. -/
@[simp]
theorem parityTwist_parityTwist (G : InternalGrading R M (ZMod 2)) (x : M) :
    G.parityTwist (G.parityTwist x) = x :=
  LinearMap.congr_fun G.parityTwist_comp_self x

/-- On an element of parity `i` of a decomposition `ℳ`, `parityTwist` acts as `(-1) ^ i`. -/
theorem parityTwist_ofDecomposition_apply_of_mem (ℳ : ZMod 2 → Submodule R M)
    [DirectSum.Decomposition ℳ] {i : ZMod 2} {x : M} (hx : x ∈ ℳ i) :
    (ofDecomposition ℳ).parityTwist x = ((-1 : ℤˣ) ^ i) • x :=
  parityTwist_apply_of_mem _ (by rwa [ofDecomposition_piece])

/-- **The parity involution of a `ZMod 2`-graded ring is multiplicative.** -/
theorem parityTwist_ofDecomposition_mul {A : Type*} [NonUnitalNonAssocRing A] [Module R A]
    {𝒜 : ZMod 2 → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] (a b : A) :
    (ofDecomposition 𝒜).parityTwist (a * b) =
      (ofDecomposition 𝒜).parityTwist a * (ofDecomposition 𝒜).parityTwist b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]
  | @homogeneous i a =>
    obtain ⟨a, hai⟩ := a
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
    | @homogeneous j b =>
      obtain ⟨b, hbj⟩ := b
      rw [parityTwist_ofDecomposition_apply_of_mem 𝒜 (SetLike.GradedMul.mul_mem hai hbj),
        parityTwist_ofDecomposition_apply_of_mem 𝒜 hai,
        parityTwist_ofDecomposition_apply_of_mem 𝒜 hbj]
      match i, j with
      | 0, 0 => simp
      | 0, 1 => simp
      | 1, 0 => simp
      | 1, 1 => simp [(by decide : (1 : ZMod 2) + 1 = 0)]

/-- The parity involution of a `ZMod 2`-graded ring fixes the unit. -/
@[simp]
theorem parityTwist_ofDecomposition_one {A : Type*} [Ring A] [Module R A]
    {𝒜 : ZMod 2 → Submodule R A} [SetLike.GradedOne 𝒜] [DirectSum.Decomposition 𝒜] :
    (ofDecomposition 𝒜).parityTwist 1 = 1 := by
  simpa using parityTwist_ofDecomposition_apply_of_mem 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜))

/-- On the parity reduction of an integer grading, `parityTwist` agrees with `koszulTwist` at
parameter `1`. -/
theorem parityTwist_parity {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    (G : InternalGrading R M ℤ) : G.parity.parityTwist = G.koszulTwist 1 := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  have hxp : x ∈ G.parity.piece (p : ZMod 2) := mem_parityGrading_of_mem hx
  rw [G.parity.parityTwist_apply_of_mem hxp, G.koszulTwist_one_apply_of_mem hx,
    uzpow_intCast, ← Int.negOnePow_def, Units.smul_def, Int.cast_smul_eq_zsmul]

end ParityTwist

end InternalGrading

end TauCeti
