/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Logic.Equiv.PartialEquiv
import TauCeti.Topology.OpenPartialHomeomorph.Germ
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Symplectic neighbourhood germs along a subset

Let `θ` and `σ` be smooth two-forms on manifolds `M` and `N`, and let `S ⊆ M`, for instance the
image of an embedded submanifold. A **symplectic neighbourhood map** along `S` is a partial
diffeomorphism `Φ` from `M` to `N` whose source contains `S` and which is a symplectic map from
`θ` to `σ` at every point of its source (`TauCeti.SmoothTwoForm.IsSymplecticMapOn`): it pulls `σ`
back to `θ` on an open neighbourhood of `S`. Two of them define the same **germ along `S`** when
they agree after shrinking around the whole of `S`, that is, when they are eventually equal for
the neighbourhood filter `𝓝ˢ S`.

The operations on partial diffeomorphisms descend to germs along subsets of their sources, as for
all open partial homeomorphisms (`TauCeti.Topology.OpenPartialHomeomorph.Germ`): inverses and
composites of germs are well defined, and differentials compose by the chain rule
(`PartialDiffeomorph.mfderiv_trans`). This file shows that the symplectic neighbourhood maps are
closed under these operations, so that symplectic neighbourhood germs have restriction, identity,
inverse and composition laws.

* **Restriction.** Restricting a symplectic neighbourhood map to an open set gives one with the
  same underlying map (`PartialDiffeomorph.isSymplecticMapOn_restrOpen`).
* **Identity.** The identity map is a symplectic map (`TauCeti.SmoothTwoForm.isSymplecticMap_id`).
* **Inverse.** The inverse of a symplectic neighbourhood map along `S` is one along `Φ(S)`
  (`PartialDiffeomorph.isSymplecticMapOn_symm`).
* **Composition.** Composites of symplectic neighbourhood maps are symplectic neighbourhood maps
  (`PartialDiffeomorph.isSymplecticMapOn_trans`).

The restriction of a germ to `S` and its ambient differentials at the points of `S` are invariants
of the germ, since a germ along `S` determines the germ at each point of `S`. The main result is
that these first-order data determine the germ up to the symplectic germs fixing `S` to first
order. Let `Φ₁` and `Φ₂` be symplectic neighbourhood maps along `S` from `θ` to `σ`. They agree at
every point of `S` and have the same differentials there exactly when there is a symplectic
neighbourhood map `Θ` along `S` from `θ` to itself, fixing every point of `S` with the identity as
differential, such that `Φ₁ = Φ₂ ∘ Θ` near `S`
(`TauCeti.SmoothTwoForm.eqOn_and_forall_mfderiv_eq_iff_exists_eventuallyEq_comp`); one can take
`Θ = Φ₂⁻¹ ∘ Φ₁`. Hence two symplectic neighbourhood germs realizing the same restriction and the
same prescribed ambient derivative along `S`, such as two outputs of
`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq` built from different auxiliary
choices, differ by a symplectic germ fixing `S` pointwise with identity ambient derivative. That
existence theorem produces diffeomorphisms between open subsets, which become symplectic
neighbourhood maps when read in the ambient manifolds
(`Diffeomorph.isSymplecticMapOn_toPartialDiffeomorph_liftOpens`).

None of these statements needs compactness of `S`, an embedding, or closedness or nondegeneracy of
the forms.

## Main results

* `PartialDiffeomorph.isSymplecticMapOn_restrOpen`, `PartialDiffeomorph.isSymplecticMapOn_symm`,
  `PartialDiffeomorph.isSymplecticMapOn_trans`: restrictions, inverses and composites of
  symplectic neighbourhood maps.
* `TauCeti.SmoothTwoForm.eqOn_and_forall_mfderiv_eq_iff_exists_eventuallyEq_comp`: two symplectic
  neighbourhood maps have the same values and differentials along `S` exactly when they differ by
  a symplectic germ fixing `S` with identity differential.
* `Diffeomorph.isSymplecticMapOn_toPartialDiffeomorph_liftOpens`: a diffeomorphism between open
  subsets pulling one restricted form back to the other is a symplectic neighbourhood map.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.4 and the neighbourhood-equivalence germs of Lectures 7 and 8.
-/

public section

open Filter Set Topology TopologicalSpace TauCeti
open scoped ContDiff Manifold

variable {E F G HE HF HG M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HE] {I : ModelWithCorners ℝ E HE}
  [TopologicalSpace M] [ChartedSpace HE M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HF] {J : ModelWithCorners ℝ F HF}
  [TopologicalSpace N] [ChartedSpace HF N] [IsManifold J ∞ N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace HG] {K : ModelWithCorners ℝ G HG}
  [TopologicalSpace P] [ChartedSpace HG P] [IsManifold K ∞ P]
  {θ : SmoothTwoForm I M} {σ : SmoothTwoForm J N} {ρ : SmoothTwoForm K P}
  {n : WithTop ℕ∞} {S : Set M}

namespace PartialDiffeomorph

/-! ### Symplectic neighbourhood maps -/

/-- **Restrictions of symplectic neighbourhood maps.** The restriction of a partial
diffeomorphism that is symplectic on its source to an open set is symplectic on its source. -/
theorem isSymplecticMapOn_restrOpen (Φ : PartialDiffeomorph I J M N n)
    (h : θ.IsSymplecticMapOn σ Φ Φ.source) {s : Set M} (hs : IsOpen s) :
    θ.IsSymplecticMapOn σ (Φ.restrOpen s hs) (Φ.restrOpen s hs).source := by
  rw [coe_restrOpen, restrOpen_source]
  exact h.mono inter_subset_left

/-- **Inverses of symplectic neighbourhood maps.** If a partial diffeomorphism of nonzero order
is a symplectic map from `θ` to `σ` on its source, its inverse is a symplectic map from `σ` to `θ`
on its target. -/
theorem isSymplecticMapOn_symm (Φ : PartialDiffeomorph I J M N n)
    (h : θ.IsSymplecticMapOn σ Φ Φ.source) (hn : n ≠ 0) :
    σ.IsSymplecticMapOn θ Φ.symm Φ.target := by
  refine SmoothTwoForm.isSymplecticMapOn_iff.2 fun y hy v w ↦ ?_
  have hx : Φ.symm y ∈ Φ.source := by
    rw [symm_toPartialEquiv]
    exact Φ.map_target hy
  have hΦy : Φ (Φ.symm y) = y := by
    rw [symm_toPartialEquiv]
    exact Φ.right_inv hy
  -- Write `v` and `w` as differentials of their images under the inverse differential.
  conv_rhs => rw [← Φ.mfderiv_apply_mfderiv_symm_apply hn hy v,
    ← Φ.mfderiv_apply_mfderiv_symm_apply hn hy w]
  refine (h.apply hx _ _).symm.trans ?_
  -- The base points `Φ (Φ⁻¹ y)` and `y` agree; the tangent spaces at both are the model space.
  rw [hΦy]

/-- **Composites of symplectic neighbourhood maps.** If partial diffeomorphisms `Φ` and `Ψ` of
nonzero order are symplectic maps on their sources, so is `Ψ ∘ Φ`. -/
theorem isSymplecticMapOn_trans (Φ : PartialDiffeomorph I J M N n)
    (Ψ : PartialDiffeomorph J K N P n) (hΦ : θ.IsSymplecticMapOn σ Φ Φ.source)
    (hΨ : σ.IsSymplecticMapOn ρ Ψ Ψ.source) (hn : n ≠ 0) :
    θ.IsSymplecticMapOn ρ (Φ.trans Ψ) (Φ.trans Ψ).source := by
  rw [coe_trans, trans_source]
  exact hΨ.comp (hΦ.mono inter_subset_left) (fun x hx ↦ hx.2)
    (fun x hx ↦ Ψ.mdifferentiableAt hn hx.2) (fun x hx ↦ Φ.mdifferentiableAt hn hx.1)

end PartialDiffeomorph

namespace Diffeomorph

/-- **Diffeomorphisms between open subsets are symplectic neighbourhood maps.** A diffeomorphism
`φ : U → V` between nonempty open subsets of `M` and `N`, pulling the restriction of `σ` to `V`
back to the restriction of `θ` to `U`, read as a partial diffeomorphism from `M` to `N`
(`PartialDiffeomorph.liftOpens`), is a symplectic map from `θ` to `σ` on its source `U`. -/
theorem isSymplecticMapOn_toPartialDiffeomorph_liftOpens {U : Opens M} {V : Opens N}
    (φ : U ≃ₘ⟮I, J⟯ V) (hU : Nonempty U) (hV : Nonempty V)
    (hφ : SmoothForm.mpullback φ φ.contMDiff
        (SmoothForm.mpullback (Subtype.val : V → N) contMDiff_subtypeVal σ) =
      SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal θ) :
    θ.IsSymplecticMapOn σ (φ.toPartialDiffeomorph.liftOpens hU hV)
      (φ.toPartialDiffeomorph.liftOpens hU hV).source := by
  -- `φ` carries `σ` to `θ` on every tangent space of `U`.
  have hφσ (z : U) (v w : TangentSpace I z) :
      SmoothBundleForm.eval₂ σ (φ z : N) (mfderiv I J φ z v) (mfderiv I J φ z w) =
        SmoothBundleForm.eval₂ θ (z : M) v w := by
    simpa only [SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val_apply] using
      congrArg (fun α : SmoothTwoForm I U ↦ SmoothBundleForm.eval₂ α z v w) hφ
  refine SmoothTwoForm.isSymplecticMapOn_iff.2 fun x hx v w ↦ ?_
  rw [PartialDiffeomorph.liftOpens_source] at hx
  obtain ⟨z, -, rfl⟩ := hx
  -- The lift has the value and the differential of `φ` at `z`. The tangent spaces of `M` at `z`
  -- and of `U` at `z`, and those of `N` and `V` at `φ z`, are all the model spaces, so `hφσ`
  -- applies to `v` and `w` as they are.
  rw [PartialDiffeomorph.mfderiv_liftOpens_apply_coe,
    PartialDiffeomorph.mfderiv_liftOpens_apply_coe, PartialDiffeomorph.liftOpens_apply_coe,
    coe_toPartialDiffeomorph]
  exact hφσ z v w

end Diffeomorph

namespace TauCeti.SmoothTwoForm

/-- **Symplectic neighbourhood germs with the same first-order data along `S`.** Let `Φ₁` and
`Φ₂` be partial diffeomorphisms of nonzero order which are symplectic maps from `θ` to `σ` on
their sources, both of which contain `S`. Then `Φ₁` and `Φ₂` take the same values and have the
same differentials at the points of `S` exactly when they differ by a symplectic germ fixing `S`
to first order: a partial diffeomorphism `Θ` of `M` whose source contains `S`, which is a
symplectic map from `θ` to itself on its source, fixes every point of `S` with the identity as
differential there, and satisfies `Φ₁ = Φ₂ ∘ Θ` near `S`. One can take `Θ = Φ₂⁻¹ ∘ Φ₁`. -/
theorem eqOn_and_forall_mfderiv_eq_iff_exists_eventuallyEq_comp
    {Φ₁ Φ₂ : PartialDiffeomorph I J M N n} (hn : n ≠ 0)
    (hΦ₁ : θ.IsSymplecticMapOn σ Φ₁ Φ₁.source) (hΦ₂ : θ.IsSymplecticMapOn σ Φ₂ Φ₂.source)
    (h₁ : S ⊆ Φ₁.source) (h₂ : S ⊆ Φ₂.source) :
    (EqOn Φ₁ Φ₂ S ∧ ∀ x ∈ S, mfderiv I J Φ₁ x = mfderiv I J Φ₂ x) ↔
      ∃ Θ : PartialDiffeomorph I I M M n, S ⊆ Θ.source ∧ θ.IsSymplecticMapOn θ Θ Θ.source ∧
        (∀ x ∈ S, Θ x = x) ∧
        (∀ x ∈ S, mfderiv I I Θ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
        ⇑Φ₁ =ᶠ[𝓝ˢ S] Φ₂ ∘ Θ := by
  refine ⟨fun ⟨h, hd⟩ ↦ ⟨Φ₁.trans Φ₂.symm,
    PartialEquiv.subset_trans_symm_source (e₁ := Φ₁.toPartialEquiv) h₁ h₂ h,
    Φ₁.isSymplecticMapOn_trans Φ₂.symm hΦ₁ (Φ₂.isSymplecticMapOn_symm hΦ₂ hn) hn,
    fun x hx ↦ PartialEquiv.trans_symm_apply_eq_self (e₁ := Φ₁.toPartialEquiv) (h₂ hx) (h hx),
    fun x hx ↦ ContinuousLinearMap.ext
      (Φ₁.mfderiv_trans_symm_apply Φ₂ hn (h₁ hx) (h₂ hx) (h hx) (hd x hx)),
    OpenPartialHomeomorph.eventuallyEq_comp_trans_symm (e₁ := Φ₁.toOpenPartialHomeomorph)
      (e₂ := Φ₂.toOpenPartialHomeomorph) h₁ h₂ h⟩, ?_⟩
  rintro ⟨Θ, hΘ, -, hΘx, hdΘ, hΦ⟩
  -- Along `S`, `Φ₁` has the value and the differential of `Φ₂ ∘ Θ`, and `Θ` is the identity there
  -- to first order.
  refine ⟨fun x hx ↦ (hΦ.self_of_nhdsSet hx).trans (congrArg Φ₂ (hΘx x hx)), fun x hx ↦ ?_⟩
  refine ContinuousLinearMap.ext fun v ↦ ((congrArg (fun L ↦ L v)
    ((hΦ.filter_mono (nhds_le_nhdsSet hx)).mfderiv_eq (I := I) (I' := J))).trans ?_)
  -- The cast between the tangent spaces at `Φ₁ x` and at `Φ₂ (Θ x)` is the identity of the model
  -- space, so it remains to apply the chain rule to `Φ₂ ∘ Θ`.
  have hcomp := mfderiv_comp_apply_of_eq x (Φ₂.mdifferentiableAt hn (h₂ hx))
    (Θ.mdifferentiableAt hn (hΘ hx)) (hΘx x hx) (v := v)
  rw [hdΘ x hx] at hcomp
  exact hcomp

end TauCeti.SmoothTwoForm
