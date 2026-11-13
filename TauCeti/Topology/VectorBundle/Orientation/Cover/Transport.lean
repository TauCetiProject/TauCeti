/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Transport of orientations along paths

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F`. Its orientation
double cover is a covering map (`TauCeti.VectorBundleOrientationCover.isCoveringMap_proj`), so a
path `γ` from `b₀` to `b₁` in the base lifts uniquely from any orientation of the fibre `E b₀`,
and the endpoint of the lift is an orientation of `E b₁`. This is the **orientation transport**
`TauCeti.VectorBundleOrientationCover.orientationTransport`, the monodromy of the orientation
double cover read on orientations of the fibres. It is canonical: no connection or
trivialization along `γ` is chosen. It does not determine a linear map between the fibres, only
which of their two orientations correspond.

Transport is an equivalence between the orientations of the two fibres, and it has the expected
laws:

* it depends only on the homotopy class of `γ` relative to its endpoints
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_eq_of_homotopic`);
* it is the identity along a constant path
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_refl`), reversing the path inverts
  it (`TauCeti.VectorBundleOrientationCover.orientationTransport_symm`), and transport along a
  concatenation is the composite
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_trans`);
* it commutes with reversal of orientations
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_neg`);
* it follows continuous families of orientations along `γ`
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_eq_of_continuous`).

The last property characterizes it: a family of orientations of the fibres along `γ` that is
continuous in the orientation double cover is the transport of its initial value.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.fiberEquiv`: the fibre of the orientation double cover
  over `b` is the set of orientations of `E b`.
* `TauCeti.VectorBundleOrientationCover.orientationTransport`: transport of orientations along a
  path.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, "The Orientation Covering".
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3 (lifting of
  paths and homotopies to covering spaces).
-/

public section

noncomputable section

open Bundle Module unitInterval

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] {ι : Type*}

variable (F E ι) in
/-- The fibre of the orientation double cover over `b` is the set of orientations of `E b`. -/
def fiberEquiv (b : B) :
    (proj : VectorBundleOrientationCover F E ι → B) ⁻¹' {b} ≃ Orientation ℝ (E b) ι where
  toFun p := Set.mem_singleton_iff.mp p.2 ▸ p.1.orientation
  invFun o := ⟨⟨b, o⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b', o⟩, h⟩
    obtain rfl : b' = b := h
    rfl
  right_inv _ := rfl

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace (TotalSpace F E)] in
@[simp]
theorem fiberEquiv_mk {b : B} (o : Orientation ℝ (E b) ι) :
    fiberEquiv F E ι b ⟨⟨b, o⟩, rfl⟩ = o :=
  (rfl)

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace (TotalSpace F E)] in
@[simp]
theorem fiberEquiv_symm_apply {b : B} (o : Orientation ℝ (E b) ι) :
    (fiberEquiv F E ι b).symm o = ⟨⟨b, o⟩, rfl⟩ :=
  (rfl)

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The deck involution, read on the fibre over `b`, is the negation of orientations. -/
theorem fiberEquiv_fiberMap_deck {b : B}
    (p : (proj : VectorBundleOrientationCover F E ι → B) ⁻¹' {b}) :
    fiberEquiv F E ι b (Function.fiberMap ⇑(deck (F := F) (E := E) (ι := ι) :
        C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι))
      proj_comp_deck b p) = -fiberEquiv F E ι b p := by
  obtain ⟨⟨b', o⟩, h⟩ := p
  obtain rfl : b' = b := h
  rw [fiberMap_deck_mk, fiberEquiv_mk, fiberEquiv_mk]

variable [Fintype ι]

variable (E) in
/-- **Transport of orientations along a path.** For a path `γ` from `b₀` to `b₁`, an orientation
`o` of `E b₀` is sent to the endpoint of the lift of `γ` to the orientation double cover starting
at `o`. This is the monodromy of the orientation double cover, which is a covering map because
`ι` has cardinality the rank of the bundle. -/
def orientationTransport (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Orientation ℝ (E b₀) ι ≃ Orientation ℝ (E b₁) ι :=
  (fiberEquiv F E ι b₀).symm.trans
    ((coveringFiberEquiv (isCoveringMap_proj hι) (.mk γ)).trans (fiberEquiv F E ι b₁))

variable (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ b₂ : B}

/-- Orientation transport is the monodromy of the orientation double cover, read on the fibres. -/
theorem orientationTransport_apply (γ : Path b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    orientationTransport E hι γ o =
      fiberEquiv F E ι b₁ ((isCoveringMap_proj hι).monodromy (.mk γ) ⟨⟨b₀, o⟩, rfl⟩) := by
  simp only [orientationTransport, Equiv.trans_apply, coveringFiberEquiv_apply,
    fiberEquiv_symm_apply]

/-- **Transport follows continuous lifts.** If `Γ` is a continuous path in the orientation double
cover lying over `γ`, transport along `γ` sends the orientation at the start of `Γ` to the
orientation at its end. -/
theorem orientationTransport_eq_of_continuous (γ : Path b₀ b₁)
    (Γ : C(I, VectorBundleOrientationCover F E ι)) (hΓ : proj ∘ Γ = γ)
    (h₀ : (Γ 0).proj = b₀) (h₁ : (Γ 1).proj = b₁) :
    orientationTransport E hι γ (fiberEquiv F E ι b₀ ⟨Γ 0, h₀⟩) =
      fiberEquiv F E ι b₁ ⟨Γ 1, h₁⟩ := by
  rw [orientationTransport_apply]
  congr 1
  exact Subtype.ext <| (isCoveringMap_proj hι).monodromy_eq_apply_one hΓ <|
    congrArg Subtype.val ((fiberEquiv F E ι b₀).symm_apply_apply ⟨Γ 0, h₀⟩).symm

/-- **Homotopy invariance.** Transport along homotopic paths, with fixed endpoints, agrees. -/
theorem orientationTransport_eq_of_homotopic {γ γ' : Path b₀ b₁} (h : γ.Homotopic γ') :
    orientationTransport E hι γ = orientationTransport E hι γ' := by
  ext1 o
  simp only [orientationTransport_apply, Path.Homotopic.Quotient.eq.mpr h]

/-- Transport along a constant path is the identity. -/
@[simp]
theorem orientationTransport_refl (b : B) :
    orientationTransport E hι (Path.refl b) = Equiv.refl (Orientation ℝ (E b) ι) := by
  ext1 o
  simp [orientationTransport_apply, Path.Homotopic.Quotient.mk_refl,
    (isCoveringMap_proj hι).monodromy_refl]

/-- Transport along a concatenation of paths is the composite of the transports. -/
theorem orientationTransport_trans (γ : Path b₀ b₁) (γ' : Path b₁ b₂) :
    orientationTransport E hι (γ.trans γ') =
      (orientationTransport E hι γ).trans (orientationTransport E hι γ') := by
  ext1 o
  simp only [orientationTransport, Equiv.trans_apply, coveringFiberEquiv_apply,
    Path.Homotopic.Quotient.mk_trans, (isCoveringMap_proj hι).monodromy_trans_apply,
    Equiv.symm_apply_apply]

/-- Transport along the reversed path is the inverse transport. -/
@[simp]
theorem orientationTransport_symm (γ : Path b₀ b₁) :
    orientationTransport E hι γ.symm = (orientationTransport E hι γ).symm := by
  rw [Equiv.eq_symm_iff_trans_eq_refl, ← orientationTransport_trans,
    orientationTransport_eq_of_homotopic hι (Path.Homotopic.symm_trans γ),
    orientationTransport_refl]

/-- **Transport commutes with reversal of orientations.** -/
@[simp]
theorem orientationTransport_neg (γ : Path b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    orientationTransport E hι γ (-o) = -orientationTransport E hι γ o := by
  let cov := isCoveringMap_proj (F := F) (E := E) hι
  rw [orientationTransport_apply, orientationTransport_apply, ← fiberMap_deck_mk,
    ← cov.fiberMap_monodromy cov _ proj_comp_deck, fiberEquiv_fiberMap_deck]

end TauCeti.VectorBundleOrientationCover
