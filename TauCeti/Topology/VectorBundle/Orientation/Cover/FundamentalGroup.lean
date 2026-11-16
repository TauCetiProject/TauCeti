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

For a real vector bundle `E → B` of rank `Fintype.card ι = finrank ℝ F`, conjugating
`TauCeti.coveringFiberEquiv` of `TauCeti.VectorBundleOrientationCover.isCoveringMap_proj` by
`TauCeti.VectorBundleOrientationCover.fiberEquiv` defines orientation transport along path homotopy
classes (`TauCeti.VectorBundleOrientationCover.quotientTransport`) and paths
(`TauCeti.VectorBundleOrientationCover.pathTransport`), commuting with negation via deck
intertwining (`TauCeti.VectorBundleOrientationCover.quotientTransport_neg`). When `F` is
finite-dimensional, every loop homotopy class at `b₀` either fixes or reverses all fibre
orientations (`TauCeti.VectorBundleOrientationCover.quotientTransport_eq_self_or_eq_neg`), defining
`TauCeti.VectorBundleOrientationCover.orientationCharacter : FundamentalGroup B b₀ →* ℤˣ`. Over a
connected, locally path-connected base, `E` is orientable if `π₁(B, b)` has no index-two subgroup
(`TauCeti.VectorBundleOrientation.nonempty_of_forall_index_ne_two`), and in particular when `B` is
simply connected (`TauCeti.VectorBundleOrientation.nonempty_of_simplyConnectedSpace`).

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
  intro u v huv; dsimp only at huv; rw [intUnits_smul_eq_ite, intUnits_smul_eq_ite] at huv
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all [Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self o).symm]

section Monodromy

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [Fintype ι]

/-- **Orientation transport along a homotopy class of paths** in the base of a real vector bundle of
rank `card ι`, obtained by conjugating `TauCeti.coveringFiberEquiv` of
`TauCeti.VectorBundleOrientationCover.isCoveringMap_proj` by `fiberEquiv`. -/
def quotientTransport (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) : Orientation ℝ (E b₀) ι ≃ Orientation ℝ (E b₁) ι :=
  ((fiberEquiv (F := F) (E := E) (ι := ι) b₀).symm.trans
    (coveringFiberEquiv (isCoveringMap_proj (F := F) (E := E) hι) γ)).trans
    (fiberEquiv (F := F) (E := E) (ι := ι) b₁)

-- Keep for explicit rewriting: `@[simp]` unfolds the LHS of `quotientTransport_neg`/`_units_smul`.
theorem quotientTransport_apply (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ o =
      fiberEquiv b₁ ((isCoveringMap_proj (F := F) (E := E) hι).monodromy γ ⟨⟨b₀, o⟩, rfl⟩) := by
  simp [quotientTransport]

@[simp]
theorem quotientTransport_refl (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    quotientTransport (F := F) (E := E) hι (.refl b) = Equiv.refl (Orientation ℝ (E b) ι) := by
  ext o; simp [quotientTransport, IsCoveringMap.monodromy_refl]

@[simp]
theorem quotientTransport_symm (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) :
    quotientTransport (F := F) (E := E) hι γ.symm =
      (quotientTransport (F := F) (E := E) hι γ).symm := by ext o; simp [quotientTransport]

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
since `VectorBundleOrientationCover.deck` intertwines covering monodromy. -/
@[simp]
theorem quotientTransport_neg (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ (-o) =
      -quotientTransport (F := F) (E := E) hι γ o := by
  set hp := isCoveringMap_proj (F := F) (E := E) hι
  let d : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι) :=
    deck (F := F) (E := E) (ι := ι)
  have hcomm := hp.fiberMap_monodromy hp d proj_comp_deck γ ⟨⟨b₀, o⟩, rfl⟩
  have hb₀ : Function.fiberMap d proj_comp_deck b₀ ⟨⟨b₀, o⟩, rfl⟩ = ⟨⟨b₀, -o⟩, rfl⟩ :=
    Subtype.ext <| by rw [Function.fiberMap_apply_coe, ContinuousMap.coe_ofClass, deck_apply]
  have hb₁ : Function.fiberMap d proj_comp_deck b₁ (hp.monodromy γ ⟨⟨b₀, o⟩, rfl⟩) =
      ⟨deck (hp.monodromy γ ⟨⟨b₀, o⟩, rfl⟩).1, (proj_deck _).trans (hp.monodromy γ _).2⟩ :=
    Subtype.ext <| by rw [Function.fiberMap_apply_coe, ContinuousMap.coe_ofClass]
  rw [quotientTransport_apply, quotientTransport_apply, ← hb₀, ← hcomm, hb₁, fiberEquiv_deck]

@[simp]
theorem quotientTransport_units_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}
    (γ : Path.Homotopic.Quotient b₀ b₁) (u : ℝˣ) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ (u • o) =
      u • quotientTransport (F := F) (E := E) hι γ o :=
  Module.Ray.units_smul_of_map_neg (quotientTransport_neg hι γ) u o

/-- **Orientation transport along a continuous path** in the base of a real vector bundle. -/
def pathTransport (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Orientation ℝ (E b₀) ι ≃ Orientation ℝ (E b₁) ι :=
  quotientTransport (F := F) (E := E) hι (.mk γ)

theorem pathTransport_def (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    pathTransport (F := F) (E := E) hι γ = quotientTransport (F := F) (E := E) hι (.mk γ) := (rfl)

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
    (γ : Path.Homotopic.Quotient b₀ b₀) : ℤˣ :=
  open Classical in if quotientTransport (F := F) (E := E) hι γ = Equiv.refl _ then 1 else -1

private theorem loopSign_refl (hι : Fintype.card ι = finrank ℝ F) (b₀ : B) :
    loopSign (F := F) (E := E) hι (.refl b₀) = 1 := by
  classical unfold loopSign; rw [quotientTransport_refl, ite_eq_left rfl]

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
  have hor (o : Orientation ℝ (E b₀) ι) : o = o₀ ∨ o = -o₀ :=
    (eq_or_eq_deck hι (p := (⟨b₀, o₀⟩ : VectorBundleOrientationCover F E ι)) (q := ⟨b₀, o⟩) rfl).imp
      mk_eq_mk_iff.1 fun h ↦ mk_eq_mk_iff.1 (by rwa [deck_apply] at h)
  refine (hor (quotientTransport (F := F) (E := E) hι γ o₀)).imp
    (fun h₀ o ↦ (hor o).elim (fun h ↦ by rw [h, h₀]) (fun h ↦ by rw [h, quotientTransport_neg, h₀]))
    (fun h₀ o ↦ (hor o).elim (fun h ↦ by rw [h, h₀]) (fun h ↦ by rw [h, quotientTransport_neg, h₀]))

private theorem loopSign_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : Path.Homotopic.Quotient b₀ b₀) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ o =
      (Units.map (Int.castRingHom ℝ).toMonoidHom (loopSign (F := F) (E := E) hι γ)) • o := by
  classical
  rw [intUnits_smul_eq_ite]; unfold loopSign; split_ifs with h₁ h₂ h₂
  · rw [h₁, Equiv.refl_apply]
  · exact absurd rfl h₂
  · exact absurd h₂ (by decide)
  · exact (quotientTransport_eq_self_or_eq_neg (F := F) (E := E) hι γ).resolve_left
      (fun h ↦ h₁ (Equiv.ext h)) o

private theorem loopSign_trans (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ₁ γ₂ : Path.Homotopic.Quotient b₀ b₀) :
    loopSign (F := F) (E := E) hι (γ₁.trans γ₂) =
      loopSign (F := F) (E := E) hι γ₂ * loopSign (F := F) (E := E) hι γ₁ := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  refine intUnits_smul_injective (fiberEquiv b₀ ⟨p₀, hp₀⟩) ?_
  dsimp only
  rw [← loopSign_smul hι (γ₁.trans γ₂), quotientTransport_trans, Equiv.trans_apply,
    loopSign_smul hι γ₁, quotientTransport_units_smul, loopSign_smul hι γ₂, map_mul, ← mul_smul,
    mul_comm]

/-- **Orientation character of a real vector bundle.** Homomorphism `FundamentalGroup B b₀ →* ℤˣ`
taking `1` on orientation-preserving loop classes and `-1` on orientation-reversing ones. -/
def orientationCharacter (hι : Fintype.card ι = finrank ℝ F) (b₀ : B) :
    FundamentalGroup B b₀ →* ℤˣ where
  toFun γ := loopSign (F := F) (E := E) hι γ.toPath
  map_one' := loopSign_refl hι b₀
  map_mul' p q := loopSign_trans hι q.toPath p.toPath

theorem quotientTransport_toPath_eq_smul (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) (o : Orientation ℝ (E b₀) ι) :
    quotientTransport (F := F) (E := E) hι γ.toPath o =
      (Units.map (Int.castRingHom ℝ).toMonoidHom
        (orientationCharacter (F := F) (E := E) hι b₀ γ)) • o :=
  loopSign_smul hι γ.toPath o

theorem orientationCharacter_eq_one_iff_apply (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) (o : Orientation ℝ (E b₀) ι) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = 1 ↔
      quotientTransport (F := F) (E := E) hι γ.toPath o = o := by
  rw [quotientTransport_toPath_eq_smul]
  exact ⟨fun h ↦ by rw [h, map_one, one_smul], fun h ↦ intUnits_smul_injective o (by simpa using h)⟩

theorem orientationCharacter_eq_neg_one_iff_apply (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) (o : Orientation ℝ (E b₀) ι) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = -1 ↔
      quotientTransport (F := F) (E := E) hι γ.toPath o = -o := by
  rw [quotientTransport_toPath_eq_smul]
  exact ⟨fun h ↦ by simp [h, Module.Ray.neg_units_smul],
    fun h ↦ intUnits_smul_injective o (by simpa [Module.Ray.neg_units_smul] using h)⟩

theorem orientationCharacter_eq_one_iff (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = 1 ↔
      quotientTransport (F := F) (E := E) hι γ.toPath = Equiv.refl _ := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  exact ⟨fun h ↦ Equiv.ext fun o ↦ (orientationCharacter_eq_one_iff_apply hι γ o).1 h, fun h ↦
    (orientationCharacter_eq_one_iff_apply hι γ (fiberEquiv b₀ ⟨p₀, hp₀⟩)).2 (by rw [h]; rfl)⟩

theorem orientationCharacter_eq_neg_one_iff (hι : Fintype.card ι = finrank ℝ F) {b₀ : B}
    (γ : FundamentalGroup B b₀) :
    orientationCharacter (F := F) (E := E) hι b₀ γ = -1 ↔
      ∀ o, quotientTransport (F := F) (E := E) hι γ.toPath o = -o := by
  obtain ⟨p₀, hp₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  exact ⟨fun h o ↦ (orientationCharacter_eq_neg_one_iff_apply hι γ o).1 h,
    fun h ↦ (orientationCharacter_eq_neg_one_iff_apply hι γ (fiberEquiv b₀ ⟨p₀, hp₀⟩)).2 (h _)⟩

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
  refine nonempty_of_forall_index_ne_two hι b fun G hG ↦ ?_
  rw [Subsingleton.elim G ⊤, Subgroup.index_top] at hG
  omega

end TauCeti.VectorBundleOrientation
