/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# The complex plane modulo integer translations

The translations `z ↦ n + z`, for `n : ℤ`, act freely and properly discontinuously on `ℂ`
by holomorphic maps. Consequently Mathlib's additive orbit carrier
`AddAction.orbitRel.Quotient ℤ ℂ`, with its installed quotient atlas, is a complex manifold,
and its orbit projection is a local biholomorphism. No new quotient carrier or atlas is used.

The action is scoped: enable it with `open scoped TauCeti.ComplexIntTranslation`.
The manifold instance then follows from `TauCeti.instIsManifoldAddQuotient` at every regularity,
including analytic regularity. The quotient is Hausdorff and connected by the
existing orbit-quotient instances, and second countable by
`ContinuousConstVAdd.secondCountableTopology`. The descent theorem below characterizes its
holomorphic maps by holomorphic functions on `ℂ` of period one.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §§4–5 (coverings and holomorphic descent).
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti.ComplexIntTranslation

/-- The action of the integers on the complex plane by translations. -/
scoped instance action : AddAction ℤ ℂ :=
  AddAction.compHom ℂ (Int.castAddHom ℂ)

/-- The integer action is translation by the corresponding complex integer. -/
@[simp]
theorem vadd_eq {n : ℤ} {z : ℂ} : n +ᵥ z = (n : ℂ) + z :=
  (rfl)

instance : ContinuousConstVAdd ℤ ℂ where
  continuous_const_vadd n := by
    simp only [vadd_eq]
    fun_prop

instance : IsCancelVAdd ℤ ℂ where
  left_cancel' _ _ _ h := add_left_cancel h
  right_cancel' _ _ _ h := Int.cast_injective (add_right_cancel h)

/-- Integer translations on the complex plane act properly discontinuously. -/
instance properlyDiscontinuousVAdd : ProperlyDiscontinuousVAdd ℤ ℂ where
  finite_disjoint_inter_image {K L} hK hL := by
    -- The translating integers lie in the compact preimage of `L - K` under the closed
    -- embedding `ℤ → ℂ`. A compact subset of the discrete space `ℤ` is finite.
    have hfinite := (Complex.isClosedEmbedding_intCast.isProperMap.isCompact_preimage
      ((hL.prod hK).image (continuous_fst.sub continuous_snd))).finite_of_discrete
    refine hfinite.subset ?_
    rintro n ⟨w, ⟨z, hz, rfl⟩, hw⟩
    exact ⟨((n : ℂ) + z, z), ⟨hw, hz⟩, by simp⟩

/-- Integer translations are complex analytic, not merely real smooth. -/
instance contMDiffConstVAdd (n : ℕ∞ω) : ContMDiffConstVAdd 𝓘(ℂ) n ℤ ℂ where
  contMDiff_const_vadd m := by
    simpa only [vadd_eq, id_eq] using (contDiff_const.add contDiff_id).contMDiff

/-- Two complex numbers define the same point of the quotient precisely when their difference
is an integer. -/
theorem quotientMk_eq_iff {z w : ℂ} :
    Quotient.mk (AddAction.orbitRel ℤ ℂ) z = Quotient.mk (AddAction.orbitRel ℤ ℂ) w ↔
      ∃ n : ℤ, (n : ℂ) + w = z := by
  rw [Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  simp only [vadd_eq]

/-- The orbit projection of the complex plane modulo integer translations is a local
`C^n` diffeomorphism over `ℂ` for every `n`, in particular a local biholomorphism at `∞`
and a local analytic diffeomorphism at `ω`. -/
theorem isLocalDiffeomorph_quotientMk (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) n (Quotient.mk (AddAction.orbitRel ℤ ℂ)) :=
  TauCeti.isLocalDiffeomorph_addQuotientMk

/-- A period-one map on the complex plane descends uniquely to a `C^n` map on the
integer-translation quotient exactly when it is `C^n` over `ℂ`. At `n = ∞` this is the
holomorphic descent property. No separation or manifold hypothesis on the codomain is needed. -/
theorem _root_.Function.Periodic.existsUnique_contMDiff_intTranslationQuotient_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    {n : ℕ∞ω} {f : ℂ → N} (hf : Function.Periodic f 1) :
    (∃! g : AddAction.orbitRel.Quotient ℤ ℂ → N,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n g ∧ ∀ z, g (Quotient.mk _ z) = f z) ↔
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n f := by
  constructor
  · rintro ⟨g, ⟨hg, hgf⟩, _⟩
    have hcomp := hg.comp (isLocalDiffeomorph_quotientMk n).contMDiff
    simpa only [Function.comp_def, hgf] using hcomp
  intro hf'
  have hinv : ∀ (m : ℤ) (z : ℂ), f (m +ᵥ z) = f z := by
    intro m z
    simpa [add_comm] using hf.int_mul m z
  let g : AddAction.orbitRel.Quotient ℤ ℂ → N := Quotient.lift f <| by
    rintro _ z ⟨m, rfl⟩
    exact hinv m z
  have hg (z : ℂ) : g (Quotient.mk _ z) = f z := rfl
  refine ⟨g, ⟨?_, hg⟩, ?_⟩
  · apply ((isLocalDiffeomorph_quotientMk n).contMDiff_comp_iff
      Quotient.mk_surjective le_rfl).1
    simpa only [Function.comp_def, hg] using hf'
  · intro g' hg'
    funext q
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
    exact (hg'.2 z).trans (hg z).symm

end TauCeti.ComplexIntTranslation
