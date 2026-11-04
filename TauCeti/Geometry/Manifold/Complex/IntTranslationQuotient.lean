/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Quotient.Descent

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

scoped instance : ContinuousConstVAdd ℤ ℂ where
  continuous_const_vadd n := by
    simp only [vadd_eq]
    fun_prop

scoped instance : IsCancelVAdd ℤ ℂ where
  left_cancel' _ _ _ h := by
    simp only [vadd_eq] at h
    exact add_left_cancel h
  right_cancel' _ _ _ h := by
    simp only [vadd_eq] at h
    exact Int.cast_injective (add_right_cancel h)

/-- Integer translations on the complex plane act properly discontinuously. -/
scoped instance properlyDiscontinuousVAdd : ProperlyDiscontinuousVAdd ℤ ℂ where
  finite_disjoint_inter_image {K L} hK hL := by
    -- The translating integers lie in the compact preimage of `L - K` under the closed
    -- embedding `ℤ → ℂ`. A compact subset of the discrete space `ℤ` is finite.
    have hfinite := (Complex.isClosedEmbedding_intCast.isProperMap.isCompact_preimage
      ((hL.prod hK).image (continuous_fst.sub continuous_snd))).finite_of_discrete
    refine hfinite.subset ?_
    rintro n ⟨w, ⟨z, hz, rfl⟩, hw⟩
    exact ⟨((n : ℂ) + z, z), ⟨hw, hz⟩, by simp⟩

/-- Integer translations are complex analytic, not merely real smooth. -/
scoped instance contMDiffConstVAdd (n : ℕ∞ω) : ContMDiffConstVAdd 𝓘(ℂ) n ℤ ℂ where
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

end TauCeti.ComplexIntTranslation

open scoped TauCeti.ComplexIntTranslation

namespace Function.Periodic

variable {N : Type*} {f : ℂ → N}

/-- The descent of a period-one map to the complex integer-translation quotient. -/
def liftIntTranslationQuotient (hf : Periodic f 1) : AddAction.orbitRel.Quotient ℤ ℂ → N :=
  TauCeti.AddAction.orbitRelQuotientLift f fun m z ↦ by
    simpa [TauCeti.ComplexIntTranslation.vadd_eq, add_comm] using hf.int_mul m z

/-- The descent takes the orbit of `z` to `f z`. -/
@[simp]
theorem liftIntTranslationQuotient_mk (hf : Periodic f 1) (z : ℂ) :
    hf.liftIntTranslationQuotient (Quotient.mk _ z) = f z :=
  TauCeti.AddAction.orbitRelQuotientLift_mk z

/-- A map on the quotient equals the period-one descent exactly when its pullback is `f`. -/
theorem eq_liftIntTranslationQuotient_iff (hf : Periodic f 1)
    {g : AddAction.orbitRel.Quotient ℤ ℂ → N} :
    g = hf.liftIntTranslationQuotient ↔ g ∘ Quotient.mk (AddAction.orbitRel ℤ ℂ) = f :=
  TauCeti.AddAction.eq_orbitRelQuotientLift_iff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}

/-- The period-one descent is `C^n` exactly when the original map is `C^n`. -/
theorem contMDiff_liftIntTranslationQuotient_iff (hf : Periodic f 1) :
    ContMDiff 𝓘(ℂ) I n hf.liftIntTranslationQuotient ↔ ContMDiff 𝓘(ℂ) I n f :=
  TauCeti.contMDiff_addOrbitRelQuotientLift_iff (n := n) le_rfl

/-- A period-one map on the complex plane descends uniquely to a `C^n` map on the
integer-translation quotient exactly when it is `C^n` over `ℂ`. At `n = ∞` this is the
holomorphic descent property. No separation or manifold hypothesis on the codomain is needed. -/
theorem existsUnique_contMDiff_intTranslationQuotient_iff (hf : Periodic f 1) :
    (∃! g : AddAction.orbitRel.Quotient ℤ ℂ → N,
      ContMDiff 𝓘(ℂ) I n g ∧ ∀ z, g (Quotient.mk _ z) = f z) ↔
      ContMDiff 𝓘(ℂ) I n f := by
  constructor
  · rintro ⟨g, ⟨hg, hgf⟩, _⟩
    rw [← hf.contMDiff_liftIntTranslationQuotient_iff]
    rwa [← hf.eq_liftIntTranslationQuotient_iff.mpr (funext hgf)]
  · intro h
    exact ⟨hf.liftIntTranslationQuotient,
      ⟨hf.contMDiff_liftIntTranslationQuotient_iff.mpr h, hf.liftIntTranslationQuotient_mk⟩,
      fun g hg ↦ hf.eq_liftIntTranslationQuotient_iff.mpr (funext hg.2)⟩

end Function.Periodic
