/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic
-- Proof-only: `QuotSMulTop` supplies the transport used to prove `length_quotient_lsmul_congr`;
-- no statement in this file mentions it.
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.QuotSMulTop

/-!
# General facts about the length of a module

Mathlib defines `Module.length R M` as the Krull dimension of the lattice of submodules and
proves that it is additive in short exact sequences. This file adds the facts about it that a
length-counting argument needs but Mathlib does not yet have: monotonicity in the submodule
quotiented by, additivity along a filtration, the length of an image, the fact that finitely
generated submodules already see the whole length, the ascent of finite length along a scalar
tower, the length of `I ⧸ aI` for an ideal `I`, the length of `R ⧸ 𝔪` for a local ring, the
finite length of a quotient of a noetherian local ring by a maximal-primary ideal, and the
infinite length of a ring of positive Krull dimension over itself.

The finite-generation reduction is the load-bearing one. `Module.length` is a supremum over
strictly increasing chains, and any *finite* chain — in particular any one witnessing a finite
lower bound on the length — is realised inside a finitely generated submodule, spanned by one
element taken from each of its steps. So a uniform bound on finitely generated submodules is a
bound on the module.

Multiplication by a ring element `a` on a module `M` is written throughout as
`LinearMap.range (LinearMap.lsmul A M a)`, which is the submodule `aM`. Mathlib spells the same
submodule pointwise, as `a • ⊤`, and quotients by it in `QuotSMulTop`. `TauCeti.map_lsmul_eq_smul`
is the single bridge between the two readings: `TauCeti.range_lsmul_eq_smul_top` and hence
`TauCeti.length_quotient_lsmul_congr` are derived from it, so that Mathlib's `QuotSMulTop` API
applies to the quotients appearing here without any further appeal to defeq.

## Main results

* `TauCeti.length_quotient_anti`: `M ⧸ Q` is no longer than `M ⧸ P` when `P ≤ Q`.
* `TauCeti.length_quotient_eq_length_map_add_length_quotient_sup`: additivity along a filtration.
* `TauCeti.length_map_mkQ`: the length of the image of `N` in `M ⧸ P`.
* `TauCeti.length_le_of_forall_fg`: a bound on all finitely generated submodules bounds the
  length.
* `TauCeti.isFiniteLength_of_tower`: finite length over `R` gives finite length over any `A`
  acting compatibly.
* `TauCeti.surjective_of_injective_of_length_eq` and
  `TauCeti.injective_of_surjective_of_length_eq`: an injective map between modules of the same
  finite length is surjective, and a surjective one is injective.
* `TauCeti.map_lsmul_eq_smul` and `TauCeti.range_lsmul_eq_smul_top`: `aN` and `aM` as Mathlib's
  pointwise `a • N` and `a • ⊤`.
* `TauCeti.comap_subtype_map_lsmul`: `aN` computed inside `N` agrees with `aN` computed in the
  ambient module.
* `TauCeti.length_quotient_lsmul_congr`: the length of `M ⧸ aM` is a linear-equivalence invariant.
* `TauCeti.length_quotient_lsmul_le_of_forall_fg`: the finite-generation reduction for `M ⧸ aM`.
* `TauCeti.isFiniteLength_quotient_of_nonZeroDivisor_mem`: `A ⧸ I` has finite length when `I`
  contains a non-zero-divisor.
* `TauCeti.isFiniteLength_of_nonZeroDivisor_mem_annihilator`: over a noetherian ring of dimension
  at most one, a finitely generated module killed by a non-zero-divisor has finite length.
* `TauCeti.length_quotient_lsmul_ideal_eq_ord`: `length (I ⧸ aI) = Ring.ord A a` for an ideal `I`
  with `A ⧸ I` of finite length.
* `TauCeti.length_quotient_maximalIdeal_eq_one`: `length (A ⧸ 𝔪) = 1` for a local ring `A`.
* `TauCeti.length_residueField_eq_one`: the residue field of a local ring `A` has length one
  over `A`.
* `TauCeti.length_self_eq_top_of_ringKrullDim_pos`: a ring of positive Krull dimension has infinite
  length over itself.
* `Ideal.isFiniteLength_quotient_of_isMaximal_radical`: `A ⧸ I` has finite length when `A` is
  noetherian and the radical of `I` is maximal. It is in the namespace of `Ideal` rather than that
  of `TauCeti` because its first explicit argument is an ideal, so that a consumer reads it as
  `I.isFiniteLength_quotient_of_isMaximal_radical`.
* `Ideal.isFiniteLength_quotient_smul_top_of_isMaximal_radical`: `M ⧸ I M` has finite length for
  a finite module `M` over a noetherian ring when the radical of `I` is maximal.
* `Ideal.length_localizedModule_quotient_eq_one`: for a prime `𝔭`, the localization of `A ⧸ 𝔭`
  at `𝔭` has length one over `A_𝔭`, being its residue field.
* `TauCeti.isFiniteLength_quotient_maximalIdeal_pow`: `A ⧸ 𝔪 ⁿ` has finite length for every `n`
  over a noetherian local ring.
* `Submodule.eq_of_le_of_length_eq`: a submodule contained in another of the same finite length
  is equal to it.
* `LinearMap.length_eq_of_bijective`: a bijective semilinear map along a surjective ring
  homomorphism preserves length.
* `LinearEquiv.length_localizedModule_comap`: for a ring isomorphism `σ : A → B` and a
  `σ`-semilinear equivalence `N ≃ M`, the localizations `N_{σ⁻¹ 𝔮}` and `M_𝔮` have the same length,
  for every prime `𝔮` of `B`.
-/

public section

namespace TauCeti

section Ring

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- Quotienting by a larger submodule cannot increase length. -/
theorem length_quotient_anti {P Q : Submodule A M} (h : P ≤ Q) :
    Module.length A (M ⧸ Q) ≤ Module.length A (M ⧸ P) := by
  rw [Module.length_quotient, Module.length_quotient]
  exact Order.coheight_anti h

/-- **Filtration additivity.** The image of `N` in `M ⧸ P` and the further quotient
`M ⧸ (P ⊔ N)` account between them for the whole of `M ⧸ P`. -/
theorem length_quotient_eq_length_map_add_length_quotient_sup (N P : Submodule A M) :
    Module.length A (M ⧸ P) = Module.length A (N.map P.mkQ) + Module.length A (M ⧸ (P ⊔ N)) := by
  rw [← (Submodule.quotientQuotientEquivQuotientSup P N).length_eq]
  exact Module.length_eq_add_of_exact (N.map P.mkQ).subtype (N.map P.mkQ).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

/-- The image of `N` in `M ⧸ P` has the length of `N ⧸ (N ⊓ P)`, for any `P`; in particular no
`P ≤ N` is needed. -/
theorem length_map_mkQ (N P : Submodule A M) :
    Module.length A (N.map P.mkQ) = Module.length A (↥N ⧸ Submodule.comap N.subtype P) := by
  have hker : LinearMap.ker (P.mkQ ∘ₗ N.subtype) = Submodule.comap N.subtype P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hran : LinearMap.range (P.mkQ ∘ₗ N.subtype) = N.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hran, ← hker]
  exact ((LinearMap.quotKerEquivRange (P.mkQ ∘ₗ N.subtype)).length_eq).symm

/-- **Length is detected by finitely generated submodules.** -/
theorem length_le_of_forall_fg {c : ℕ∞} (h : ∀ N : Submodule A M, N.FG → Module.length A N ≤ c) :
    Module.length A M ≤ c := by
  rw [Module.length_eq_height, Order.height_le_iff]
  intro l _
  -- Pick a witness for each strict step of `l`, and span them: the chain survives inside that span.
  have hx : ∀ i : Fin l.length, ∃ x : M, x ∈ l i.succ ∧ x ∉ l i.castSucc := fun i =>
    IsConcreteLE.exists_of_lt (l.strictMono i.castSucc_lt_succ)
  choose x hx1 hx2 using hx
  set N : Submodule A M := Submodule.span A (Set.range x)
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hmono : StrictMono (fun i => Submodule.comap N.subtype (l i)) :=
    Fin.strictMono_iff_lt_succ.mpr fun i => IsConcreteLE.lt_iff_le_and_exists.mpr
      ⟨Submodule.comap_mono (l.strictMono i.castSucc_lt_succ).le, ⟨x i, hxN i⟩, hx1 i, hx2 i⟩
  refine le_trans ?_ (h N (Submodule.fg_span (Set.finite_range x)))
  rw [Module.length_eq_height]
  exact Order.length_le_height (p := .mk l.length _ hmono) le_top

/-- **Finite length ascends along a scalar tower.** A module of finite length over `R` has finite
length over any `S` acting compatibly, since its `S`-submodules are among its `R`-submodules. -/
theorem isFiniteLength_of_tower (R : Type*) [Ring R] [SMul R A] [Module R M]
    [IsScalarTower R A M] (h : IsFiniteLength R M) : IsFiniteLength A M := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower R inferInstance, isArtinian_of_tower R inferInstance⟩

/-- An injective linear map between modules of the same finite length is surjective: its
cokernel has length zero. -/
theorem surjective_of_injective_of_length_eq {N : Type*} [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Injective f) (hM : Module.length A M ≠ ⊤)
    (h : Module.length A M = Module.length A N) : Function.Surjective f := by
  have hlen := Module.length_eq_add_of_exact _ _ hf (Submodule.mkQ_surjective _)
    (LinearMap.exact_map_mkQ_range f)
  rw [← h] at hlen
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff,
    ← Module.length_eq_zero_iff (R := A)]
  exact WithTop.add_left_cancel hM (hlen.symm.trans (add_zero _).symm)

/-- A surjective linear map between modules of the same finite length is injective: its kernel
has length zero. -/
theorem injective_of_surjective_of_length_eq {N : Type*} [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Surjective f) (hN : Module.length A N ≠ ⊤)
    (h : Module.length A M = Module.length A N) : Function.Injective f := by
  have hlen := Module.length_eq_add_of_exact _ _ (LinearMap.ker f).injective_subtype hf
    (LinearMap.exact_subtype_ker_map f)
  rw [h] at hlen
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
    ← Module.length_eq_zero_iff (R := A)]
  exact WithTop.add_right_cancel hN (hlen.symm.trans (zero_add _).symm)

end Ring

section CommSemiring

open scoped Pointwise

variable {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- `aN`, written as the image of the submodule `N` under multiplication by `a`, is the pointwise
scalar multiple `a • N`. This is the only bridge between the two readings of `aN`; the rest of
this file meets Mathlib's pointwise API through it. -/
theorem map_lsmul_eq_smul (N : Submodule A M) (a : A) :
    N.map (LinearMap.lsmul A M a) = a • N := by
  rw [Submodule.pointwise_smul_def]
  exact congrArg (fun f : M →ₗ[A] M => Submodule.map f N) (LinearMap.ext fun _ => rfl)

/-- `aM`, written as the range of multiplication by `a`, is the pointwise scalar multiple
`a • ⊤` that Mathlib's `QuotSMulTop` quotients by. -/
theorem range_lsmul_eq_smul_top (a : A) :
    LinearMap.range (LinearMap.lsmul A M a) = a • (⊤ : Submodule A M) := by
  rw [← map_lsmul_eq_smul, Submodule.map_top]

/-- For a submodule `N`, the elements of `N` lying in `aN` computed in the ambient module are
exactly the elements of `aN` computed in `N`. -/
@[simp]
theorem comap_subtype_map_lsmul (N : Submodule A M) (a : A) :
    Submodule.comap N.subtype (N.map (LinearMap.lsmul A M a))
      = LinearMap.range (LinearMap.lsmul A ↥N a) := by
  ext y
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_map,
    LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(z : M), z.2, rfl⟩

end CommSemiring

section CommRing

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The length of `M ⧸ aM` depends on `M` only through its linear equivalence class.

This proves nothing that Mathlib does not: it is `QuotSMulTop.congr` read through
`range_lsmul_eq_smul_top`, and exists only so that the change of spelling is not repeated at each
call site. It is stated forward-only, because rewriting back out of a `QuotSMulTop`-shaped goal is
not type-correct — the `AddCommGroup` instance on the quotient depends on the submodule being
rewritten. -/
theorem length_quotient_lsmul_congr {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (a : A) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a))
      = Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N a)) := by
  rw [range_lsmul_eq_smul_top, range_lsmul_eq_smul_top]
  exact (QuotSMulTop.congr a e).length_eq

/-- **Reduction of the length of `M ⧸ aM` to finitely generated submodules.** -/
theorem length_quotient_lsmul_le_of_forall_fg {a : A} {c : ℕ∞} (h : ∀ N : Submodule A M, N.FG →
      Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) ≤ c) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a)) ≤ c := by
  set P : Submodule A M := LinearMap.range (LinearMap.lsmul A M a)
  refine length_le_of_forall_fg fun Q hQ => ?_
  -- A finitely generated submodule of `M ⧸ aM` is the image of a finitely generated `N ≤ M`.
  obtain ⟨s, hs⟩ := hQ
  choose g hg using Submodule.mkQ_surjective P
  set N : Submodule A M := Submodule.span A (g '' (s : Set (M ⧸ P))) with hN
  have hNfg : N.FG := Submodule.fg_span (s.finite_toSet.image _)
  have hQeq : Q = N.map P.mkQ := by
    rw [hN, Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    simp [hg]
  have hle : LinearMap.range (LinearMap.lsmul A ↥N a) ≤ Submodule.comap N.subtype P := by
    rintro y ⟨z, rfl⟩
    exact ⟨(z : M), rfl⟩
  calc Module.length A ↥Q = Module.length A ↥(N.map P.mkQ) := by rw [hQeq]
    _ = Module.length A (↥N ⧸ Submodule.comap N.subtype P) := length_map_mkQ N P
    _ ≤ Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) :=
        length_quotient_anti hle
    _ ≤ c := h N hNfg

/-- In a Noetherian ring of Krull dimension at most one, the quotient by an ideal containing a
non-zero-divisor has finite length. -/
theorem isFiniteLength_quotient_of_nonZeroDivisor_mem [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    (I : Ideal A) {x : A} (hxI : x ∈ I) (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (A ⧸ I) := by
  have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
  exact (isFiniteLength_quotient_span_singleton A hx).of_surjective
    (f := Submodule.factor hle) (Submodule.factor_surjective hle)

/-- In a Noetherian ring of Krull dimension at most one, a finitely generated module whose
annihilator contains a non-zero-divisor has finite length. -/
theorem isFiniteLength_of_nonZeroDivisor_mem_annihilator [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Module.Finite A M] {x : A} (hxM : x ∈ Module.annihilator A M)
    (hx : x ∈ nonZeroDivisors A) : IsFiniteLength A M := by
  -- `M` is a finitely generated module over the Artinian ring `A ⧸ Ann(M)`.
  let _ := Module.quotientAnnihilator (R := A) (M := M)
  obtain ⟨-, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (isFiniteLength_quotient_of_nonZeroDivisor_mem (Module.annihilator A M) hxM hx)
  have : IsArtinianRing (A ⧸ Module.annihilator A M) := isArtinian_of_tower A inferInstance
  have : Module.Finite (A ⧸ Module.annihilator A M) M :=
    Module.Finite.of_restrictScalars_finite A _ M
  have : IsArtinian A M :=
    isArtinian_of_surjective_algebraMap (R := A ⧸ Module.annihilator A M)
      Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, this⟩

/-- **The length of `I ⧸ aI` for an ideal `I`.** For an ideal `I` with `A ⧸ I` of finite length
and a non-zero-divisor `a`, `length (I ⧸ aI)` is the order of vanishing `Ring.ord A a`, which is
by definition `length (A ⧸ aA)`.

Both sides are read off `length (A ⧸ aI)`, which splits in two ways. Mathlib's exact sequence
`A ⧸ I ↪ A ⧸ aI ↠ A ⧸ aA` — multiplication by `a`, then quotienting further, from
`Ideal.exact_mulQuot_quotOfMul` — splits it as `length (A ⧸ I) + length (A ⧸ aA)`, while the
filtration `aI ≤ I ≤ A` splits it as `length (I ⧸ aI) + length (A ⧸ I)`. Cancelling the common
term, finite by hypothesis, leaves the claim. -/
theorem length_quotient_lsmul_ideal_eq_ord (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) (a : A)
    (ha : a ∈ nonZeroDivisors A) :
    Module.length A (↥I ⧸ LinearMap.range (LinearMap.lsmul A ↥I a)) = Ring.ord A a := by
  have hord : Ring.ord A a = Module.length A (A ⧸ Ideal.span {a}) := rfl
  have hfin : Module.length A (A ⧸ I) ≠ ⊤ := Module.length_ne_top_iff.mpr hI
  have hexact : Module.length A (A ⧸ Submodule.map (LinearMap.lsmul A A a) I)
      = Module.length A (A ⧸ I) + Module.length A (A ⧸ Ideal.span {a}) := by
    rw [map_lsmul_eq_smul]
    exact Module.length_eq_add_of_exact (Ideal.mulQuot a I) (Ideal.quotOfMul a I)
      (Ideal.mulQuot_injective I ha) (Ideal.quotOfMul_surjective I)
      (Ideal.exact_mulQuot_quotOfMul I)
  -- The filtration `aI ≤ I ≤ A` splits the same length the other way.
  have hleI : Submodule.map (LinearMap.lsmul A A a) I ⊔ I = I := by
    refine sup_eq_right.mpr ?_
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    simpa [LinearMap.lsmul_apply] using I.smul_mem a hx
  have hfilt := length_quotient_eq_length_map_add_length_quotient_sup I
    (Submodule.map (LinearMap.lsmul A A a) I)
  rw [hleI, length_map_mkQ, comap_subtype_map_lsmul, hexact] at hfilt
  rw [hord]
  exact (WithTop.add_left_cancel hfin (hfilt.trans (add_comm _ _))).symm

end CommRing

section LocalRing

open _root_.IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- The length of a quotient by the maximal ideal of a local ring is one, the quotient being the
residue field. -/
@[simp]
theorem length_quotient_maximalIdeal_eq_one : Module.length A (A ⧸ maximalIdeal A) = 1 :=
  Module.length_eq_one_iff.mpr (isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal A).out)

/-- The residue field of a local ring has length one over the ring. -/
@[simp]
theorem length_residueField_eq_one : Module.length A (ResidueField A) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (S := ResidueField A) residue_surjective]
  exact instIsSimpleModule _

end LocalRing

end TauCeti

namespace Ideal

section NoetherianRing

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

/-- **A quotient by an ideal with maximal radical has finite length.** Let `A` be a noetherian ring
and `I` an ideal whose radical is a maximal ideal `𝔪`, so that `I` is `𝔪`-primary. Then `A ⧸ I`
has finite length over `A`. -/
theorem isFiniteLength_quotient_of_isMaximal_radical (I : Ideal A) (hI : I.radical.IsMaximal) :
    IsFiniteLength A (A ⧸ I) := by
  -- `𝔪` is the only prime over `I`, so `A ⧸ I` is a noetherian ring of dimension zero.
  have : Ring.KrullDimLE 0 (A ⧸ I) :=
    krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun J hJ ↦ by
      have := hI.isPrime
      rw [← radical_minimalPrimes, minimalPrimes_eq_subsingleton_self] at hJ
      exact Set.mem_singleton_iff.mp hJ ▸ hI
  have : IsArtinianRing (A ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩

/-- **A finite module modulo an ideal with maximal radical has finite length.** Let `A` be a
noetherian ring, `I` an ideal whose radical is a maximal ideal and `M` a finite `A`-module. Then
`M ⧸ I M` is a finite module over the Artinian ring `A ⧸ I`, so it has finite length over `A`. -/
theorem isFiniteLength_quotient_smul_top_of_isMaximal_radical (I : Ideal A)
    (hI : I.radical.IsMaximal) (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsFiniteLength A (M ⧸ (I • ⊤ : Submodule A M)) := by
  have hA := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (isFiniteLength_quotient_of_isMaximal_radical I hI)
  have : IsArtinianRing (A ⧸ I) := isArtinian_of_tower A hA.2
  have : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, isArtinian_of_surjective_algebraMap (R := A ⧸ I) Ideal.Quotient.mk_surjective⟩

end NoetherianRing

section NoetherianLocalRing

open _root_.IsLocalRing

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Every quotient of a noetherian local ring by a power of its maximal ideal has finite length:
for `n ≠ 0` the power `𝔪 ⁿ` is maximal-primary, and for `n = 0` the quotient is zero. -/
theorem _root_.TauCeti.isFiniteLength_quotient_maximalIdeal_pow (n : ℕ) :
    IsFiniteLength A (A ⧸ maximalIdeal A ^ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (A ⧸ maximalIdeal A ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact .of_subsingleton
  · exact isFiniteLength_quotient_of_isMaximal_radical _ <| by
      rw [radical_pow _ hn, (maximalIdeal.isMaximal A).isPrime.radical]
      infer_instance

end NoetherianLocalRing

section Localization

variable {A : Type*} [CommRing A]

/-- **The localization of `A ⧸ 𝔭` at `𝔭` has length one.** For a prime `𝔭` of a commutative ring
`A`, the localization `(A ⧸ 𝔭)_𝔭` is the quotient of `A_𝔭` by `𝔭 A_𝔭`, its maximal ideal, so it is
the residue field of `A_𝔭` and a simple `A_𝔭`-module. -/
@[simp]
theorem length_localizedModule_quotient_eq_one (𝔭 : Ideal A) [𝔭.IsPrime] :
    Module.length (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl (A ⧸ 𝔭)) = 1 := by
  have := IsLocalization.linearMap_compatibleSMul 𝔭.primeCompl (Localization.AtPrime 𝔭)
  let e := (IsLocalizedModule.linearEquiv 𝔭.primeCompl
    (𝔭.toLocalizedQuotient' (Localization.AtPrime 𝔭) 𝔭.primeCompl
      (Algebra.linearMap A (Localization.AtPrime 𝔭)))
    (LocalizedModule.mkLinearMap 𝔭.primeCompl (A ⧸ 𝔭))).restrictScalars (Localization.AtPrime 𝔭)
  rw [← e.length_eq, Ideal.localized'_eq_map, Localization.AtPrime.map_eq_maximalIdeal,
    TauCeti.length_quotient_maximalIdeal_eq_one]

end Localization

end Ideal

namespace TauCeti

section PositiveKrullDimension

variable {A : Type*} [CommRing A]

/-- **A ring of positive Krull dimension has infinite length over itself**, since a ring of finite
length over itself is Artinian, hence of Krull dimension zero. Positivity cannot be weakened to
`ringKrullDim A ≠ 0`: the trivial ring, whose `ringKrullDim` is `⊥`, has length zero over itself.

In particular the length of a one-dimensional local domain over itself is infinite, which is what
a length read along such a domain, the order of vanishing of an element of it, has to be measured
against. -/
@[simp]
theorem length_self_eq_top_of_ringKrullDim_pos (hpos : 0 < ringKrullDim A) :
    Module.length A A = ⊤ := by
  by_contra h
  have : IsArtinianRing A :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h)).2
  exact hpos.not_ge (Ring.krullDimLE_iff.mp inferInstance)

end PositiveKrullDimension

end TauCeti

namespace Submodule

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- A submodule contained in another of the same finite length is equal to it: the inclusion is
an injective map between modules of the same finite length, hence surjective. -/
theorem eq_of_le_of_length_eq {N P : Submodule A M} (h : N ≤ P) (hN : Module.length A N ≠ ⊤)
    (hlen : Module.length A N = Module.length A P) : N = P := by
  have hs := TauCeti.surjective_of_injective_of_length_eq (inclusion_injective h) hN hlen
  rw [← LinearMap.range_eq_top, range_inclusion, comap_subtype_eq_top] at hs
  exact le_antisymm h hs

end Submodule

namespace LinearMap

variable {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module S N] {σ : R →+* S} [RingHomSurjective σ]

/-- **A bijective semilinear map preserves length.** Along a surjective ring homomorphism `σ`, a
bijective `σ`-semilinear map identifies the lattices of submodules of its source and target, so
the two modules have the same length. -/
theorem length_eq_of_bijective (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

end LinearMap

namespace LinearEquiv

variable {A B N M : Type*} [CommRing A] [CommRing B] [AddCommGroup N] [Module A N]
  [AddCommGroup M] [Module B M] {σ : A →+* B} {σ' : B →+* A} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/-- The localization `n / s ↦ e n / σ s` of a `σ`-semilinear equivalence at a prime `𝔮` of `B`
and its preimage `σ⁻¹ 𝔮`, semilinear along the induced map of local rings. It serves only to
compare the lengths of the two localizations in `length_localizedModule_comap`. -/
private noncomputable def localizedModuleComap (e : N ≃ₛₗ[σ] M) (𝔮 : Ideal B) [𝔮.IsPrime] :
    LocalizedModule (𝔮.comap σ).primeCompl N →ₛₗ[Localization.localRingHom (𝔮.comap σ) 𝔮 σ rfl]
      LocalizedModule 𝔮.primeCompl M where
  toFun x := x.liftOn (fun p ↦ LocalizedModule.mk (e p.1) ⟨σ p.2, p.2.2⟩) fun ⟨n, s⟩ ⟨n', s'⟩
      ⟨u, hu⟩ ↦ LocalizedModule.mk_eq.mpr ⟨⟨σ u, u.2⟩, by
        simpa [Submonoid.smul_def, map_smulₛₗ] using congrArg e hu⟩
  map_add' x y := by
    induction x using LocalizedModule.induction_on with | h n s => ?_
    induction y using LocalizedModule.induction_on with | h n' s' => ?_
    simp [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, Submonoid.smul_def, map_smulₛₗ]
    -- The denominators `⟨σ s * σ s', _⟩` and `⟨σ s, _⟩ * ⟨σ s', _⟩` agree in the submonoid.
    rfl
  map_smul' c x := by
    induction c using Localization.induction_on with | H p => ?_
    induction x using LocalizedModule.induction_on with | h n t => ?_
    simp [LocalizedModule.mk_smul_mk, LocalizedModule.liftOn_mk, Localization.localRingHom_mk,
      map_smulₛₗ]
    -- As in `map_add'`, the two denominators agree in the submonoid.
    rfl

private theorem localizedModuleComap_mk (e : N ≃ₛₗ[σ] M) (𝔮 : Ideal B) [𝔮.IsPrime] (n : N)
    (s : (𝔮.comap σ).primeCompl) :
    localizedModuleComap e 𝔮 (LocalizedModule.mk n s) = LocalizedModule.mk (e n) ⟨σ s, s.2⟩ :=
  rfl

/-- **Transport of local lengths along a ring isomorphism.** Let `σ : A → B` be a ring isomorphism
and `e : N ≃ M` a `σ`-semilinear equivalence from an `A`-module to a `B`-module. For every prime
`𝔮` of `B`, the localization of `N` at `σ⁻¹ 𝔮` has the same length over `A_{σ⁻¹ 𝔮}` as the
localization of `M` at `𝔮` over `B_𝔮`. -/
theorem length_localizedModule_comap (e : N ≃ₛₗ[σ] M) (𝔮 : Ideal B) [𝔮.IsPrime] :
    Module.length (Localization.AtPrime (𝔮.comap σ)) (LocalizedModule (𝔮.comap σ).primeCompl N) =
      Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl M) := by
  have hσ (b : B) : σ (σ' b) = b := RingHomInvPair.comp_apply_eq₂
  have hmem (t : 𝔮.primeCompl) : σ' t ∈ (𝔮.comap σ).primeCompl := by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_comap, hσ]
    exact t.2
  have : RingHomSurjective (Localization.localRingHom (𝔮.comap σ) 𝔮 σ rfl) :=
    ⟨(Localization.localRingEquiv (𝔮.comap σ) 𝔮 (RingHomInvPair.toRingEquiv σ σ') rfl).surjective⟩
  refine LinearMap.length_eq_of_bijective (localizedModuleComap e 𝔮) ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · induction x using LocalizedModule.induction_on with | h n s => ?_
    induction y using LocalizedModule.induction_on with | h n' s' => ?_
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp (by simpa [localizedModuleComap_mk] using hxy)
    refine LocalizedModule.mk_eq.mpr ⟨⟨σ' u, hmem u⟩, e.injective ?_⟩
    simpa [Submonoid.smul_def, map_smulₛₗ, hσ] using hu
  · induction y using LocalizedModule.induction_on with | h m t => ?_
    exact ⟨LocalizedModule.mk (e.symm m) ⟨σ' t, hmem t⟩, by simp [localizedModuleComap_mk, hσ]⟩

end LinearEquiv
