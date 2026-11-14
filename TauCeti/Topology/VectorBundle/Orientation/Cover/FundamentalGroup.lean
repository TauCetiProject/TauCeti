/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.IsLocalHomeomorph
import TauCeti.LinearAlgebra.Ray
import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Covering-monodromy orientation transport, orientation character, and orientability from `π₁`

For a real vector bundle `E → B` of rank `Fintype.card ι = finrank ℝ F`, the projection of its
orientation double cover `TauCeti.VectorBundleOrientationCover` is a covering map
(`TauCeti.VectorBundleOrientationCover.isCoveringMap_proj`). Conjugating
`TauCeti.coveringFiberEquiv` by `TauCeti.VectorBundleOrientationCover.fiberEquiv` defines
orientation transport along endpoint-relative path homotopy classes
(`TauCeti.VectorBundleOrientationCover.quotientTransport`) and paths
(`TauCeti.VectorBundleOrientationCover.pathTransport`). Because the deck involution reverses fibre
orientations and commutes with covering monodromy (`IsCoveringMap.fiberMap_monodromy`), orientation
transport commutes with negation (`TauCeti.VectorBundleOrientationCover.quotientTransport_neg`).

When `F` is finite-dimensional, every loop homotopy class at `b₀` either fixes every orientation of
`E b₀` or reverses every orientation
(`TauCeti.VectorBundleOrientationCover.quotientTransport_eq_self_or_eq_neg`), assembling into the
orientation character
`TauCeti.VectorBundleOrientationCover.orientationCharacter : FundamentalGroup B b₀ →* ℤˣ`.

Over a connected, locally path-connected base, `E` is orientable if `π₁(B, b)` has no subgroup of
index two (`TauCeti.VectorBundleOrientation.nonempty_of_forall_index_ne_two`). In particular, every
finite-rank real vector bundle over a simply connected, locally path-connected base is orientable
(`TauCeti.VectorBundleOrientation.nonempty_of_simplyConnectedSpace`).

## Main definitions

* `TauCeti.VectorBundleOrientationCover.quotientTransport`: orientation transport
  `Orientation ℝ (E b₀) ι ≃ Orientation ℝ (E b₁) ι` along `Path.Homotopic.Quotient b₀ b₁`.
* `TauCeti.VectorBundleOrientationCover.pathTransport`: orientation transport along `Path b₀ b₁`.
* `TauCeti.VectorBundleOrientationCover.orientationCharacter`: the loop monodromy homomorphism
  `FundamentalGroup B b₀ →* ℤˣ`.

## Main results

* `TauCeti.VectorBundleOrientationCover.quotientTransport_neg`: orientation transport commutes with
  reversing orientations.
* `TauCeti.VectorBundleOrientationCover.quotientTransport_toPath_eq_smul`,
  `TauCeti.VectorBundleOrientationCover.orientationCharacter_eq_one_iff`,
  `TauCeti.VectorBundleOrientationCover.orientationCharacter_eq_neg_one_iff`: action and sign
  characterizations of `orientationCharacter`.
* `TauCeti.VectorBundleOrientation.nonempty_of_forall_index_ne_two`,
  `TauCeti.VectorBundleOrientation.nonempty_of_simplyConnectedSpace`: orientability criteria from
  the fundamental group.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218, Springer, 2013,
  Chapter 15, The Orientation Covering.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.32
  (the number of sheets is the index of the induced subgroup).
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti.VectorBundleOrientationCover

private theorem intUnits_smul_eq_ite {M ι : Type*} [AddCommMonoid M] [Module ℝ M]
    (u : ℤˣ) (o : Orientation ℝ M ι) :
    (Units.map (Int.castRingHom ℝ).toMonoidHom u) • o = if u = 1 then o else -o := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [Module.Ray.neg_units_smul]

private theorem intUnits_smul_injective {M ι : Type*} [AddCommMonoid M] [Module ℝ M]
    (o : Orientation ℝ M ι) :
    Function.Injective (fun u : ℤˣ ↦ (Units.map (Int.castRingHom ℝ).toMonoidHom u) • o) := by
  intro u v huv
  dsimp only at huv
  rw [intUnits_smul_eq_ite, intUnits_smul_eq_ite] at huv
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all [Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self o).symm]

section Monodromy

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]

/-- **Orientation transport along a homotopy class of paths** in the base of a real vector bundle of
rank `card ι`, obtained by conjugating `TauCeti.coveringFiberEquiv` of
`TauCeti.VectorBundleOrientationCover.isCoveringMap_proj` by
`TauCeti.VectorBundleOrientationCover.fiberEquiv`. -/
def quotientTransport (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) :
    Orientation ℝ (E b₀) ι ≃ Orientation ℝ (E b₁) ι :=
  ((fiberEquiv (F := F) (E := E) (ι := ι) b₀).symm.trans
    (coveringFiberEquiv (isCoveringMap_proj (F := F) (E := E) hι) γ)).trans
    (fiberEquiv (F := F) (E := E) (ι := ι) b₁)

-- Keep this lemma for explicit rewriting: a simp attribute unfolds the left-hand side of
-- `quotientTransport_neg` and `quotientTransport_units_smul`, failing the `simpNF` linter.
theorem quotientTransport_apply (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ o =
      fiberEquiv b₁ ((isCoveringMap_proj (F := F) (E := E) hι).monodromy γ ⟨⟨b₀, o⟩, rfl⟩) := by
  simp [quotientTransport]

@[simp]
theorem quotientTransport_refl (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    quotientTransport (F := F) (E := E) hι (Path.Homotopic.Quotient.refl b) =
      Equiv.refl (Orientation ℝ (E b) ι) := by
  ext o
  simp [quotientTransport, IsCoveringMap.monodromy_refl]

@[simp]
theorem quotientTransport_symm (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) :
    quotientTransport (F := F) (E := E) hι γ.symm =
      (quotientTransport (F := F) (E := E) hι γ).symm := by
  ext o
  simp [quotientTransport]

/-- Concatenation law for `VectorBundleOrientationCover.quotientTransport`. -/
theorem quotientTransport_trans (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ b₂ : B}
    (γ₁ : Path.Homotopic.Quotient b₀ b₁) (γ₂ : Path.Homotopic.Quotient b₁ b₂) :
    quotientTransport (F := F) (E := E) hι (γ₁.trans γ₂) =
      (quotientTransport (F := F) (E := E) hι γ₁).trans
        (quotientTransport (F := F) (E := E) hι γ₂) := by
  ext o
  rw [quotientTransport_apply, Equiv.trans_apply, quotientTransport_apply, quotientTransport_apply,
    ← fiberEquiv_symm_apply b₁, Equiv.symm_apply_apply,
    (isCoveringMap_proj (F := F) (E := E) hι).monodromy_trans_apply]

/-- Orientation transport along a homotopy class of paths commutes with reversing orientations,
because the deck involution `VectorBundleOrientationCover.deck` intertwines covering monodromy. -/
@[simp]
theorem quotientTransport_neg (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ (-o) =
      -quotientTransport (F := F) (E := E) hι γ o := by
  set hp := isCoveringMap_proj (F := F) (E := E) hι
  let d : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι) :=
    deck (F := F) (E := E) (ι := ι)
  have hcomm := hp.fiberMap_monodromy hp d proj_comp_deck γ ⟨⟨b₀, o⟩, rfl⟩
  have hb₀ : Function.fiberMap d proj_comp_deck b₀ ⟨⟨b₀, o⟩, rfl⟩ = ⟨⟨b₀, -o⟩, rfl⟩ := by
    apply Subtype.ext
    rw [Function.fiberMap_apply_coe, ContinuousMap.coe_ofClass, deck_apply]
  have hb₁ : Function.fiberMap d proj_comp_deck b₁ (hp.monodromy γ ⟨⟨b₀, o⟩, rfl⟩) =
      ⟨deck (hp.monodromy γ ⟨⟨b₀, o⟩, rfl⟩).1,
        (proj_deck _).trans (hp.monodromy γ ⟨⟨b₀, o⟩, rfl⟩).2⟩ := by
    apply Subtype.ext
    rw [Function.fiberMap_apply_coe, ContinuousMap.coe_ofClass]
  rw [quotientTransport_apply, quotientTransport_apply, ← hb₀, ← hcomm, hb₁, fiberEquiv_deck]

@[simp]
theorem quotientTransport_units_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) (u : ℝˣ) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ (u • o) =
      u • quotientTransport (F := F) (E := E) hι γ o :=
  Module.Ray.units_smul_of_map_neg (quotientTransport_neg hι γ) u o

/-- **Orientation transport along a continuous path** in the base of a real vector bundle of rank
`card ι`. -/
def pathTransport (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Orientation ℝ (E b₀) ι ≃ Orientation ℝ (E b₁) ι :=
  quotientTransport (F := F) (E := E) hι (.mk γ)

theorem pathTransport_def (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    pathTransport (F := F) (E := E) hι γ = quotientTransport (F := F) (E := E) hι (.mk γ) :=
  (rfl)

@[simp]
theorem pathTransport_refl (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    pathTransport (F := F) (E := E) hι (Path.refl b) = Equiv.refl (Orientation ℝ (E b) ι) :=
  quotientTransport_refl hι b

@[simp]
theorem pathTransport_symm (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    pathTransport (F := F) (E := E) hι γ.symm = (pathTransport (F := F) (E := E) hι γ).symm :=
  quotientTransport_symm hι (.mk γ)

theorem pathTransport_trans (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ b₂ : B}
    (γ₁ : Path b₀ b₁) (γ₂ : Path b₁ b₂) :
    pathTransport (F := F) (E := E) hι (γ₁.trans γ₂) =
      (pathTransport (F := F) (E := E) hι γ₁).trans (pathTransport (F := F) (E := E) hι γ₂) :=
  quotientTransport_trans hι (.mk γ₁) (.mk γ₂)

theorem pathTransport_eq_of_homotopic (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    {γ₁ γ₂ : Path b₀ b₁} (h : γ₁.Homotopic γ₂) :
    pathTransport (F := F) (E := E) hι γ₁ = pathTransport (F := F) (E := E) hι γ₂ :=
  congrArg (quotientTransport (F := F) (E := E) hι) (Quotient.sound h)

@[simp]
theorem pathTransport_neg (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁)
    (o : Orientation ℝ (E b₀) ι) :
    pathTransport (F := F) (E := E) hι γ (-o) = -pathTransport (F := F) (E := E) hι γ o :=
  quotientTransport_neg hι (.mk γ) o

@[simp]
theorem pathTransport_units_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁)
    (u : ℝˣ) (o : Orientation ℝ (E b₀) ι) :
    pathTransport (F := F) (E := E) hι γ (u • o) = u • pathTransport (F := F) (E := E) hι γ o :=
  quotientTransport_units_smul hι (.mk γ) u o

private def loopSign (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : Path.Homotopic.Quotient b₀ b₀) : ℤˣ := by
  classical
  exact if quotientTransport (F := F) (E := E) hι γ = Equiv.refl _ then 1 else -1

private theorem loopSign_refl (hι : Fintype.card ι = finrank ℝ F) (b₀ : B) :
    loopSign (F := F) (E := E) hι (.refl b₀) = 1 := by
  classical
  unfold loopSign
  rw [quotientTransport_refl, ite_eq_left rfl]

section FiniteDimensional

variable [FiniteDimensional ℝ F]

/-- Around any loop homotopy class based at `b₀`, orientation transport either fixes every fibre
orientation or reverses every fibre orientation. -/
theorem quotientTransport_eq_self_or_eq_neg (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : Path.Homotopic.Quotient b₀ b₀) :
    (∀ o, quotientTransport (F := F) (E := E) hι γ o = o) ∨
      (∀ o, quotientTransport (F := F) (E := E) hι γ o = -o) := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  let o₀ : Orientation ℝ (E b₀) ι := fiberEquiv b₀ ⟨p₀, hp₀⟩
  have hor (o : Orientation ℝ (E b₀) ι) : o = o₀ ∨ o = -o₀ := by
    rcases eq_or_eq_deck hι (p := (⟨b₀, o₀⟩ : VectorBundleOrientationCover F E ι))
      (q := ⟨b₀, o⟩) rfl with h | h
    · exact .inl (mk_eq_mk_iff.1 h)
    · rw [deck_apply] at h
      exact .inr (mk_eq_mk_iff.1 h)
  rcases hor (quotientTransport (F := F) (E := E) hι γ o₀) with h₀ | h₀
  · refine .inl fun o ↦ ?_
    rcases hor o with rfl | rfl
    · exact h₀
    · rw [quotientTransport_neg, h₀]
  · refine .inr fun o ↦ ?_
    rcases hor o with rfl | rfl
    · exact h₀
    · rw [quotientTransport_neg, h₀]

private theorem loopSign_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : Path.Homotopic.Quotient b₀ b₀) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ o =
      (Units.map (Int.castRingHom ℝ).toMonoidHom (loopSign (F := F) (E := E) hι γ)) • o := by
  classical
  rw [intUnits_smul_eq_ite]
  unfold loopSign
  split_ifs with h₁ h₂ h₂
  · rw [h₁, Equiv.refl_apply]
  · exact absurd rfl h₂
  · exact absurd h₂ (by decide)
  · rcases quotientTransport_eq_self_or_eq_neg (F := F) (E := E) hι γ with h | h
    · exact absurd (Equiv.ext h) h₁
    · exact h o

private theorem loopSign_trans (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ₁ γ₂ : Path.Homotopic.Quotient b₀ b₀) :
    loopSign (F := F) (E := E) hι (γ₁.trans γ₂) =
      loopSign (F := F) (E := E) hι γ₂ * loopSign (F := F) (E := E) hι γ₁ := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  let o₀ : Orientation ℝ (E b₀) ι := fiberEquiv b₀ ⟨p₀, hp₀⟩
  apply intUnits_smul_injective o₀
  dsimp only
  rw [← loopSign_smul hι (γ₁.trans γ₂) o₀, quotientTransport_trans, Equiv.trans_apply,
    loopSign_smul hι γ₁ o₀, quotientTransport_units_smul, loopSign_smul hι γ₂ o₀, map_mul,
    ← mul_smul, mul_comm]

/-- **Orientation character of a real vector bundle.** Homomorphism from `FundamentalGroup B b₀` to
`ℤˣ` taking value `1` on orientation-preserving loop classes and `-1` on orientation-reversing loop
classes. -/
def orientationCharacter (hι : Fintype.card ι = finrank ℝ F) (b₀ : B) :
    FundamentalGroup B b₀ →* ℤˣ where
  toFun γ := loopSign (F := F) (E := E) hι γ.toPath
  map_one' := loopSign_refl hι b₀
  map_mul' p q := loopSign_trans hι q.toPath p.toPath

/-- Orientation transport along a loop class `γ : FundamentalGroup B b₀` acts on every orientation
of `E b₀` by its `orientationCharacter` sign. -/
theorem quotientTransport_toPath_eq_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ.toPath o =
      (Units.map (Int.castRingHom ℝ).toMonoidHom
        (orientationCharacter (F := F) (E := E) hι b₀ γ)) • o :=
  loopSign_smul hι γ.toPath o

/-- `orientationCharacter` equals `1` if and only if orientation transport along `γ` fixes a given
orientation `o` of `E b₀`. -/
theorem orientationCharacter_eq_one_iff_apply (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) (o : Orientation ℝ (E b₀) ι) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = 1 ↔
      quotientTransport (F := F) (E := E) hι γ.toPath o = o := by
  rw [quotientTransport_toPath_eq_smul]
  refine ⟨fun h ↦ by rw [h, map_one, one_smul], fun h ↦ intUnits_smul_injective o ?_⟩
  simpa using h

/-- `orientationCharacter` equals `-1` if and only if orientation transport along `γ` reverses a
given orientation `o` of `E b₀`. -/
theorem orientationCharacter_eq_neg_one_iff_apply (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) (o : Orientation ℝ (E b₀) ι) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = -1 ↔
      quotientTransport (F := F) (E := E) hι γ.toPath o = -o := by
  rw [quotientTransport_toPath_eq_smul]
  refine ⟨fun h ↦ by simp [h, Module.Ray.neg_units_smul],
    fun h ↦ intUnits_smul_injective o ?_⟩
  simpa [Module.Ray.neg_units_smul] using h

/-- `orientationCharacter` equals `1` if and only if orientation transport along `γ` is the identity
equivalence of `Orientation ℝ (E b₀) ι`. -/
theorem orientationCharacter_eq_one_iff (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = 1 ↔
      quotientTransport (F := F) (E := E) hι γ.toPath = Equiv.refl _ := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  let o₀ : Orientation ℝ (E b₀) ι := fiberEquiv b₀ ⟨p₀, hp₀⟩
  refine ⟨fun h ↦ Equiv.ext fun o ↦ (orientationCharacter_eq_one_iff_apply hι γ o).1 h,
    fun h ↦ (orientationCharacter_eq_one_iff_apply hι γ o₀).2 ?_⟩
  rw [h, Equiv.refl_apply]

/-- `orientationCharacter` equals `-1` if and only if orientation transport along `γ` reverses every
orientation of `E b₀`. -/
theorem orientationCharacter_eq_neg_one_iff (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = -1 ↔
      ∀ o, quotientTransport (F := F) (E := E) hι γ.toPath o = -o := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  let o₀ : Orientation ℝ (E b₀) ι := fiberEquiv b₀ ⟨p₀, hp₀⟩
  refine ⟨fun h o ↦ (orientationCharacter_eq_neg_one_iff_apply hι γ o).1 h,
    fun h ↦ (orientationCharacter_eq_neg_one_iff_apply hι γ o₀).2 (h o₀)⟩

end FiniteDimensional

end Monodromy

end TauCeti.VectorBundleOrientationCover

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B] [LocallyPathConnectedSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]

/-- A real vector bundle over a connected, locally path-connected base whose fundamental group
has no subgroup of index two is orientable, provided `ι` has cardinality the rank of the bundle. -/
theorem nonempty_of_forall_index_ne_two [ConnectedSpace B]
    (hι : Fintype.card ι = finrank ℝ F) (b : B)
    (hπ : ∀ G : Subgroup (FundamentalGroup B b), G.index ≠ 2) :
    Nonempty (VectorBundleOrientation F E ι) := by
  apply (nonempty_iff_not_connectedSpace hι).mpr
  intro hc
  have : ConnectedSpace (VectorBundleOrientationCover F E ι) := hc
  have hp := VectorBundleOrientationCover.isCoveringMap_proj (F := F) (E := E) hι
  have : LocallyPathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨p, hp₀⟩ := VectorBundleOrientationCover.surjective_proj (F := F) (E := E) hι b
  have hcard := hp.card_fiber_eq_index ⟨p, hp₀⟩
  rw [Nat.card_coe_set_eq, VectorBundleOrientationCover.ncard_fiber hι] at hcard
  exact hπ _ hcard.symm

/-- A real vector bundle over a simply connected, locally path-connected base is orientable,
provided `ι` has cardinality the rank of the bundle. -/
theorem nonempty_of_simplyConnectedSpace [SimplyConnectedSpace B]
    (hι : Fintype.card ι = finrank ℝ F) : Nonempty (VectorBundleOrientation F E ι) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  apply nonempty_of_forall_index_ne_two hι b
  intro G hG
  have hindex : G.index = 1 := by
    rw [Subsingleton.elim G ⊤, Subgroup.index_top]
  omega

end TauCeti.VectorBundleOrientation
