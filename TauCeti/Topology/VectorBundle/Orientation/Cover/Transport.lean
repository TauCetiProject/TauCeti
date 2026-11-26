/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Fiberwise
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Transport of orientations along paths

Let `E → B` be a real vector bundle with model fibre `F`, and let `ι` be a finite index type with
`Fintype.card ι = finrank ℝ F`. When `F` is finite-dimensional, this chooses top-degree
orientations: an orientation of a fibre `E b` indexed by `ι` is an orientation of `E b` in the
usual sense. (When `F` is infinite-dimensional, `finrank ℝ F = 0`, so `ι` is empty and the
construction transports degree-zero data instead.) The orientation double cover is then a covering
map (`TauCeti.VectorBundleOrientationCover.isCoveringMap_proj`), so a path `γ` from `b₀` to `b₁`
in the base lifts uniquely from any orientation of the fibre `E b₀`, and the endpoint of the lift
is an orientation of `E b₁`. This is the **orientation transport**
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
* it is natural: a fibrewise isomorphism of bundles over a continuous map `g` of bases, with
  continuous total-space map, carries transport along `γ` to transport along the image of `γ`
  under `g` (`TauCeti.VectorBundleOrientationCover.orientationTransport_map`);
* it follows lifts of `γ` to the orientation double cover
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_eq_of_lift`).

The last property characterizes it: a family of orientations of the fibres along `γ` that is
continuous in the orientation double cover is the transport of its initial value.

For the determinant line bundle `TauCeti.FredholmDetLine ℝ E F` of real Fredholm operators, a line
bundle, the caller chooses the model fibre `F := ℝ` and `ι := Fin 1`, and supplies the condition
`Fintype.card (Fin 1) = finrank ℝ ℝ`, proved by `simp`; the covering-map proof is constructed by
`orientationTransport` itself. Transport then carries orientations of determinant lines along
continuous paths of Fredholm operators, which is how orientations of moduli spaces in Morse and
Floer theory are compared along paths of operators. The module
`TauCeti.Analysis.Fredholm.DeterminantLine.Transport` transports orientations along
real-parameter families of operators directly, through coherent families of elements in kernel
charts (`TauCeti.detLineOrientationTransport`), without forming the bundle or its cover.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.orientationTransport`: transport of orientations along a
  path.

## Main results

* `TauCeti.VectorBundleOrientationCover.orientationTransport_eq_of_homotopic`: transport depends
  only on the homotopy class of the path relative to its endpoints.
* `TauCeti.VectorBundleOrientationCover.orientationTransport_map`: naturality of transport under
  fibrewise isomorphisms of bundles.

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

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] [Fintype ι]

variable (E) in
/-- **Transport of orientations along a path.** For a path `γ` from `b₀` to `b₁`, an orientation
`o` of `E b₀` is sent to the endpoint of the lift of `γ` to the orientation double cover starting
at `o`. This is the monodromy of the orientation double cover, which is a covering map because
`hι : Fintype.card ι = finrank ℝ F`. For finite-dimensional `F` these are top-degree orientations
of the fibres. -/
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

/-- **Transport follows lifts.** If `Γ` is a continuous path in the orientation double cover lying
over `γ`, transport along `γ` sends the orientation at the start of `Γ` to the orientation at its
end. -/
theorem orientationTransport_eq_of_lift (γ : Path b₀ b₁)
    (Γ : C(I, VectorBundleOrientationCover F E ι)) (hΓ : proj ∘ Γ = γ)
    (h₀ : (Γ 0).proj = b₀) (h₁ : (Γ 1).proj = b₁) :
    orientationTransport E hι γ (fiberEquiv F E ι b₀ ⟨Γ 0, h₀⟩) =
      fiberEquiv F E ι b₁ ⟨Γ 1, h₁⟩ := by
  rw [orientationTransport_apply]
  congr 1
  exact Subtype.ext <| (isCoveringMap_proj hι).monodromy_eq_apply_one hΓ <|
    congrArg Subtype.val ((fiberEquiv_symm_apply _).symm.trans
      ((fiberEquiv F E ι b₀).symm_apply_apply ⟨Γ 0, h₀⟩)).symm

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
  ext1 o
  simp only [orientationTransport, Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    coveringFiberEquiv_apply, coveringFiberEquiv_symm_apply, Path.Homotopic.Quotient.mk_symm]

/-- **Transport commutes with reversal of orientations.** -/
@[simp]
theorem orientationTransport_neg (γ : Path b₀ b₁) (o : Orientation ℝ (E b₀) ι) :
    orientationTransport E hι γ (-o) = -orientationTransport E hι γ o := by
  let cov := isCoveringMap_proj (F := F) (E := E) hι
  rw [orientationTransport_apply, orientationTransport_apply, ← fiberMap_deck_mk,
    ← cov.fiberMap_monodromy cov _ proj_comp_deck, fiberEquiv_fiberMap_deck]

section Map

variable {B' : Type*} [TopologicalSpace B']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {E' : B' → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  {g : C(B', B)} {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}

/-- **Naturality of transport.** A fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over a
continuous map `g`, with continuous total-space map, carries transport along `γ` in `E'` to
transport along the image of `γ` under `g` in `E`. -/
theorem orientationTransport_map (hι' : Fintype.card ι = finrank ℝ F')
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))
    {b₀ b₁ : B'} (γ : Path b₀ b₁) (o : Orientation ℝ (E' b₀) ι) :
    orientationTransport E hι (γ.map g.continuous) (o.map ι (φ b₀).toLinearEquiv) =
      (orientationTransport E' hι' γ o).map ι (φ b₁).toLinearEquiv := by
  have h := (isCoveringMap_proj hι').coe_monodromy_map (isCoveringMap_proj hι)
    (g := map hι' hφ) (f := g) (funext (proj_map hι' hφ)) (.mk γ) ⟨⟨b₀, o⟩, rfl⟩
    ⟨⟨g b₀, o.map ι (φ b₀).toLinearEquiv⟩, rfl⟩ (map_mk ..)
  rw [← Path.Homotopic.Quotient.mk_map] at h
  rw [orientationTransport_apply, orientationTransport_apply]
  obtain ⟨o', ho'⟩ := (fiberEquiv F' E' ι b₁).symm.surjective
    ((isCoveringMap_proj hι').monodromy (.mk γ) ⟨⟨b₀, o⟩, rfl⟩)
  rw [← ho', fiberEquiv_symm_apply, map_mk] at h
  rw [← ho', Equiv.apply_symm_apply, ← Equiv.eq_symm_apply, fiberEquiv_symm_apply]
  exact Subtype.ext h

end Map

end TauCeti.VectorBundleOrientationCover
