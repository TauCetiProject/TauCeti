/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.RingTheory.Huber.ModuleTopology.StablyPseudoCoherent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
import TauCeti.RingTheory.Huber.LocalizationTopology.Iterated
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Pseudoflat modules and base change of stable pseudocoherence

Let `A` be a topological commutative ring and `m ∈ ℕ ∪ {∞}`. Following Kedlaya and Liu
(*Relative p-adic Hodge theory, II*, §2.4, Definition 2.4.4), an `A`-module `B` is
*`m`-pseudoflat* over `A` if `Tor₁^A(Q, B) = 0` for every stably `m`-pseudocoherent `A`-module `Q`.
Concretely, for every submodule `K` of a finite free module `Fin n → A` whose quotient
`(Fin n → A) ⧸ K` is stably `m`-pseudocoherent over `A`, the base-changed inclusion
`K ⊗[A] B → (Fin n → A) ⊗[A] B` is injective.

Splitting a finite projective module off a finite free module extends this vanishing of `Tor₁` to
every short exact sequence `0 → M → N → P → 0` with `N` finite projective and `P` stably
`m`-pseudocoherent (`TauCeti.Huber.IsPseudoFlat.rTensor_injective` and
`TauCeti.Huber.isPseudoFlat_iff_injective_rTensor`).

When `B` is a commutative `A`-algebra that is `2`-pseudoflat over `A`, base change along `A → B`
carries stably `2`-pseudocoherent `A`-modules to `2`-pseudocoherent `B`-modules
(`TauCeti.Huber.IsPseudoFlat.isPseudoCoherentOver_two_baseChange`): the first syzygy of a stably
`2`-pseudocoherent module is finitely presented, and `2`-pseudoflatness keeps the inclusion of that
syzygy injective after tensoring with `B`, preserving exactness at the middle term of a two-step
free presentation.

For a completed rational localisation `B = A⟨T/s⟩` whose numerators span an open ideal, iterated
rational localisations of `B` are topologically `A`-algebra-isomorphic to single rational
localisations of `A` (`TauCeti.Huber.exists_ratLoc_ringEquiv_ratLoc`). Consequently, any
`B`-base change `B ⊗[A] M` of a stably pseudocoherent `A`-module `M` already satisfies the analytic
half of stable pseudocoherence over `B`
(`TauCeti.Huber.IsStablyPseudoCoherent.ratLoc_of_isPseudoCoherentOver`). Combining the two halves
yields Kedlaya–Liu II, Remark 2.4.5: if `A⟨T/s⟩` is `2`-pseudoflat over `A`, then base change to
`A⟨T/s⟩` preserves stable `2`-pseudocoherence (`TauCeti.Huber.IsStablyPseudoCoherent.ratLoc_two`),
and `2`-pseudoflatness composes across `A → A⟨T/s⟩` (`TauCeti.Huber.IsPseudoFlat.comp_ratLoc`).

## Main definitions

* `TauCeti.Huber.IsPseudoFlat A B m`: the `A`-module `B` is `m`-pseudoflat over `A`.

## Main results

* `TauCeti.Huber.IsPseudoFlat.mono`, `TauCeti.Huber.IsPseudoFlat.of_flat`,
  `TauCeti.Huber.IsPseudoFlat.of_equiv`, `TauCeti.Huber.IsPseudoFlat.of_retract`,
  `TauCeti.Huber.IsPseudoFlat.prod`: monotonicity in `m`, flatness implies pseudoflatness, and
  stability under linear equivalences, retracts and binary products.
* `TauCeti.Huber.IsPseudoFlat.rTensor_injective` and
  `TauCeti.Huber.isPseudoFlat_iff_injective_rTensor`: characterisation via short exact sequences
  with finite projective middle term.
* `TauCeti.Huber.IsPseudoFlat.isPseudoCoherentOver_two_baseChange`: `2`-pseudoflatness carries
  stably `2`-pseudocoherent modules to `2`-pseudocoherent modules.
* `TauCeti.Huber.exists_ratLoc_ringEquiv_ratLoc`: an iterated completed rational localisation with
  open numerator ideals is topologically `A`-isomorphic to a single completed rational localisation.
* `TauCeti.Huber.IsStablyPseudoCoherent.ratLoc_of_isPseudoCoherentOver` and
  `TauCeti.Huber.IsStablyPseudoCoherent.ratLoc_two`: base change of stable pseudocoherence to a
  rational localisation.
* `TauCeti.Huber.IsPseudoFlat.comp_of_forall_baseChange` and
  `TauCeti.Huber.IsPseudoFlat.comp_ratLoc`: composition of pseudoflatness along rational
  localisations.
* `TauCeti.Huber.not_isPseudoFlat_quotient_span_singleton`: a principal quotient `A ⧸ (f)` by a
  non-unit regular element is not `m`-pseudoflat whenever it is stably `m`-pseudocoherent.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Definition 2.4.4 and Remark 2.4.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 8.2 and Remark 8.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Huber

universe u v

section Definition

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (B : Type v) [AddCommGroup B] [Module A B]

/-- An `A`-module `B` is *`m`-pseudoflat* over `A` if, for every submodule `K` of a finite free
module `Fin n → A` whose quotient `(Fin n → A) ⧸ K` is stably `m`-pseudocoherent over `A`, the
induced map `K ⊗[A] B → (Fin n → A) ⊗[A] B` is injective (Kedlaya–Liu II, Definition 2.4.4). -/
def IsPseudoFlat (m : ℕ∞) : Prop :=
  ∀ (n : ℕ) (K : Submodule A (Fin n → A)),
    IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m → Function.Injective (K.subtype.rTensor B)

theorem isPseudoFlat_iff {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {B : Type v} [AddCommGroup B] [Module A B] {m : ℕ∞} :
    IsPseudoFlat A B m ↔
      ∀ (n : ℕ) (K : Submodule A (Fin n → A)),
        IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m →
          Function.Injective (K.subtype.rTensor B) :=
  (Iff.rfl)

end Definition

namespace IsPseudoFlat

section Basic

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {B : Type v} [AddCommGroup B] [Module A B] {m : ℕ∞}

/-- `m`-pseudoflatness implies `m'`-pseudoflatness for `m ≤ m'`: stably `m'`-pseudocoherent
quotients are in particular stably `m`-pseudocoherent. -/
theorem mono {m' : ℕ∞} (h : IsPseudoFlat A B m) (hm : m ≤ m') : IsPseudoFlat A B m' :=
  fun n K hK ↦ h n K (hK.mono hm)

/-- Every flat `A`-module is `m`-pseudoflat for every `m`. -/
theorem of_flat [Module.Flat A B] : IsPseudoFlat A B m :=
  fun _ K _ ↦ Module.Flat.rTensor_preserves_injective_linearMap K.subtype K.injective_subtype

/-- Every topological commutative ring is `m`-pseudoflat over itself. -/
theorem self : IsPseudoFlat A A m :=
  of_flat

/-- If `B'` is a linear retract of an `m`-pseudoflat `A`-module `B`, then `B'` is `m`-pseudoflat. -/
theorem of_retract {B' : Type*} [AddCommGroup B'] [Module A B'] {i : B' →ₗ[A] B} {r : B →ₗ[A] B'}
    (hri : r ∘ₗ i = LinearMap.id) (h : IsPseudoFlat A B m) : IsPseudoFlat A B' m := by
  intro n K hK
  have hli : LinearMap.lTensor K r ∘ₗ LinearMap.lTensor K i = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hri, LinearMap.lTensor_id]
  have hinj_i : Function.Injective (LinearMap.lTensor K i) :=
    Function.LeftInverse.injective fun x ↦ congr($hli x)
  have hsq : LinearMap.lTensor (Fin n → A) i ∘ₗ K.subtype.rTensor B' =
      K.subtype.rTensor B ∘ₗ LinearMap.lTensor K i := by
    ext k b'
    rfl
  exact Function.Injective.of_comp (f := LinearMap.lTensor (Fin n → A) i) <| by
    rw [← LinearMap.coe_comp, hsq]
    exact (h n K hK).comp hinj_i

/-- `m`-pseudoflatness is invariant under `A`-linear equivalence. -/
theorem of_equiv {B' : Type*} [AddCommGroup B'] [Module A B'] (e : B ≃ₗ[A] B')
    (h : IsPseudoFlat A B m) : IsPseudoFlat A B' m :=
  h.of_retract (i := e.symm.toLinearMap) (r := e.toLinearMap) (LinearMap.ext e.apply_symm_apply)

/-- A binary product of `m`-pseudoflat modules is `m`-pseudoflat. -/
theorem prod {B' : Type*} [AddCommGroup B'] [Module A B'] (h₁ : IsPseudoFlat A B m)
    (h₂ : IsPseudoFlat A B' m) : IsPseudoFlat A (B × B') m := by
  intro n K hK z₁ z₂ hz
  rw [← sub_eq_zero]
  set z := z₁ - z₂
  have hz₀ : K.subtype.rTensor (B × B') z = 0 := by rw [map_sub, hz, sub_self]
  let p₁ := LinearMap.fst A B B'
  let p₂ := LinearMap.snd A B B'
  let j₁ := LinearMap.inl A B B'
  let j₂ := LinearMap.inr A B B'
  have hsq₁ : K.subtype.rTensor B (LinearMap.lTensor K p₁ z) =
      LinearMap.lTensor (Fin n → A) p₁ (K.subtype.rTensor (B × B') z) := by
    induction z using TensorProduct.inductionOn with
    | tmul k x => rfl
    | add x y ihx ihy => simp [map_add, ihx, ihy]
  have hsq₂ : K.subtype.rTensor B' (LinearMap.lTensor K p₂ z) =
      LinearMap.lTensor (Fin n → A) p₂ (K.subtype.rTensor (B × B') z) := by
    induction z using TensorProduct.inductionOn with
    | tmul k x => rfl
    | add x y ihx ihy => simp [map_add, ihx, ihy]
  rw [hz₀, map_zero] at hsq₁ hsq₂
  have hz₁ : LinearMap.lTensor K p₁ z = 0 :=
    (h₁ n K hK) (hsq₁.trans (map_zero _).symm)
  have hz₂ : LinearMap.lTensor K p₂ z = 0 :=
    (h₂ n K hK) (hsq₂.trans (map_zero _).symm)
  have hid : j₁ ∘ₗ p₁ + j₂ ∘ₗ p₂ = LinearMap.id := by
    ext x <;> simp [j₁, j₂, p₁, p₂]
  calc z = LinearMap.lTensor K (LinearMap.id : (B × B') →ₗ[A] (B × B')) z := by simp
    _ = LinearMap.lTensor K (j₁ ∘ₗ p₁ + j₂ ∘ₗ p₂) z := by rw [hid]
    _ = LinearMap.lTensor K j₁ (LinearMap.lTensor K p₁ z) +
          LinearMap.lTensor K j₂ (LinearMap.lTensor K p₂ z) := by
        rw [LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp,
          LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    _ = 0 := by simp [hz₁, hz₂]

/-- **Projective presentation form of pseudoflatness** (Kedlaya–Liu II, Definition 2.4.4). For any
short exact sequence `0 → M →[i] N →[p] P → 0` of `A`-modules with `N` finite projective and `P`
stably `m`-pseudocoherent, `i ⊗ 1_B : M ⊗[A] B → N ⊗[A] B` is injective. -/
theorem rTensor_injective {M N P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N]
    [AddCommGroup P] [Module A P] {i : M →ₗ[A] N} {p : N →ₗ[A] P}
    (hB : IsPseudoFlat A B m) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsStablyPseudoCoherent A P m) :
    Function.Injective (i.rTensor B) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A N
  have hf : Function.Surjective f := Function.RightInverse.surjective fun x ↦ congr($hfg x)
  set q : (Fin n → A) →ₗ[A] P := p ∘ₗ f
  have hq : Function.Surjective q := hp.comp hf
  set K : Submodule A (Fin n → A) := LinearMap.ker q
  have hK : IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m :=
    hP.of_equiv (q.quotKerEquivOfSurjective hq).symm
  let gK : M →ₗ[A] K := (g ∘ₗ i).codRestrict K fun x ↦ by
    have hfg_i : f (g (i x)) = i x := congr($hfg (i x))
    simp [K, q, hfg_i, hexact.apply_apply_eq_zero x]
  have hrange : ∀ k : K, f k.1 ∈ LinearMap.range i := fun k ↦ (hexact (f k.1)).mp k.2
  let fK : K →ₗ[A] M :=
    (LinearEquiv.ofInjective i hi).symm.toLinearMap ∘ₗ (f ∘ₗ K.subtype).codRestrict _ hrange
  have hfKgK : fK ∘ₗ gK = LinearMap.id := by
    ext x
    apply hi
    dsimp [fK, gK]
    have happ : (⟨i ((LinearEquiv.ofInjective i hi).symm ⟨f (g (i x)), hrange (gK x)⟩),
        ⟨_, rfl⟩⟩ : LinearMap.range i) = ⟨f (g (i x)), hrange (gK x)⟩ :=
      (LinearEquiv.ofInjective i hi).apply_symm_apply _
    exact (congrArg Subtype.val happ).trans congr($hfg (i x))
  have hr_gK : Function.Injective (gK.rTensor B) := by
    have hli : fK.rTensor B ∘ₗ gK.rTensor B = LinearMap.id := by
      rw [← LinearMap.rTensor_comp, hfKgK, LinearMap.rTensor_id]
    exact Function.LeftInverse.injective fun z ↦ congr($hli z)
  have hcomp : g.rTensor B ∘ₗ i.rTensor B = K.subtype.rTensor B ∘ₗ gK.rTensor B := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
    rfl
  exact Function.Injective.of_comp (f := g.rTensor B) <| by
    rw [← LinearMap.coe_comp, hcomp]
    exact (hB n K hK).comp hr_gK

end Basic

end IsPseudoFlat

/-- **Characterisation of `m`-pseudoflatness via projective short exact sequences**
(Kedlaya–Liu II, Definition 2.4.4). -/
theorem isPseudoFlat_iff_injective_rTensor {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type v} [AddCommGroup B] [Module A B] {m : ℕ∞} :
    IsPseudoFlat A B m ↔
      ∀ (M N P : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
        [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
        (i : M →ₗ[A] N) (p : N →ₗ[A] P),
        Function.Injective i → Function.Surjective p → Function.Exact i p →
        IsStablyPseudoCoherent A P m → Function.Injective (i.rTensor B) :=
  ⟨fun h _ _ _ _ _ _ _ _ _ _ _ _ _ hi hp hex hP ↦ h.rTensor_injective hi hp hex hP,
    fun h n K hK ↦ h K (Fin n → A) ((Fin n → A) ⧸ K) K.subtype K.mkQ
      K.injective_subtype (Submodule.mkQ_surjective K) (LinearMap.exact_subtype_mkQ K) hK⟩

/-! ### Degree-`2` base change of pseudocoherence -/

namespace IsPseudoFlat

private theorem injective_baseChange_of_injective_rTensor {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Injective (f.rTensor B)) :
    Function.Injective (f.baseChange B) := by
  rw [LinearMap.baseChange_eq_lTensor]
  have hconj : (TensorProduct.comm A B N).toLinearMap ∘ₗ LinearMap.lTensor B f =
      f.rTensor B ∘ₗ (TensorProduct.comm A B M).toLinearMap := by
    ext b m
    rfl
  exact Function.Injective.of_comp (f := (TensorProduct.comm A B N).toLinearMap) <| by
    rw [← LinearMap.coe_comp, hconj]
    exact hf.comp (TensorProduct.comm A B M).injective

/-- **Algebraic half of Kedlaya–Liu II, Remark 2.4.5.** If `B` is an `m`-pseudoflat commutative
`A`-algebra with `2 ≤ m` and `M` is stably `m`-pseudocoherent over `A`, then `B ⊗[A] M` is
`2`-pseudocoherent over `B`. -/
theorem isPseudoCoherentOver_two_of_le {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [Algebra A B] {M : Type*} [AddCommGroup M]
    [Module A M] {m : ℕ∞} (hB : IsPseudoFlat A B m) (hM : IsStablyPseudoCoherent A M m)
    (hm : 2 ≤ m) : IsPseudoCoherentOver B (B ⊗[A] M) 2 := by
  classical
  -- Unpack a free `2`-step resolution `A^n₂ → A^n₁ → A^n₀ → M → 0` over `A`.
  have hM2 : IsPseudoCoherentOver A M ((1 : ℕ∞) + 1) := hM.isPseudoCoherentOver.mono hm
  obtain ⟨n₀, ε, hε, hK₀⟩ := IsPseudoCoherentOver.succ_iff.mp hM2
  set K₀ := LinearMap.ker ε
  have hK₀_stably : IsStablyPseudoCoherent A ((Fin n₀ → A) ⧸ K₀) m :=
    hM.of_equiv (ε.quotKerEquivOfSurjective hε).symm
  have hinj_base : Function.Injective (K₀.subtype.baseChange B) :=
    injective_baseChange_of_injective_rTensor (hB n₀ K₀ hK₀_stably)
  have hK₀' : IsPseudoCoherentOver A K₀ ((0 : ℕ∞) + 1) := by simpa using hK₀
  obtain ⟨n₁, q, hq, hK₁⟩ := IsPseudoCoherentOver.succ_iff.mp hK₀'
  have : Module.Finite A (LinearMap.ker q) := IsPseudoCoherentOver.zero_iff.mp hK₁
  obtain ⟨n₂, r, hr⟩ := Module.Finite.exists_fin' A (LinearMap.ker q)
  let d₀ : (Fin n₁ → A) →ₗ[A] (Fin n₀ → A) := K₀.subtype ∘ₗ q
  let d₁ : (Fin n₂ → A) →ₗ[A] (Fin n₁ → A) := (LinearMap.ker q).subtype ∘ₗ r
  have hex₀ : Function.Exact d₀ ε :=
    hq.comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map ε)
  have hex₁ : Function.Exact d₁ q :=
    hr.comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map q)
  -- Base-change the resolution to `B` and identify `B ⊗[A] (Fin k → A) ≃ₗ[B] (Fin k → B)`.
  let e (k : ℕ) := TensorProduct.piScalarRight A B B (Fin k)
  let rk : ℕ → ℕ
    | 0 => n₀
    | 1 => n₁
    | 2 => n₂
    | _ + 3 => 0
  let diff : ∀ i, (Fin (rk (i + 1)) → B) →ₗ[B] (Fin (rk i) → B)
    | 0 => (e n₀).toLinearMap ∘ₗ d₀.baseChange B ∘ₗ (e n₁).symm.toLinearMap
    | 1 => (e n₁).toLinearMap ∘ₗ d₁.baseChange B ∘ₗ (e n₂).symm.toLinearMap
    | _ + 2 => 0
  rw [isPseudoCoherentOver_iff]
  refine ⟨rk, diff, ε.baseChange B ∘ₗ (e n₀).symm.toLinearMap,
    (ε.baseChange_surjective B hε).comp (e n₀).symm.surjective, fun _ ↦ ?_, fun i hi ↦ ?_⟩
  · dsimp only [rk, diff]
    rw [← LinearMap.comp_assoc, LinearEquiv.precomp_exact_iff_exact,
      LinearEquiv.conj_exact_iff_exact]
    simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact B hex₀ hε
  · rcases i with _ | i
    · dsimp only [rk, diff]
      rw [← LinearMap.comp_assoc, LinearEquiv.precomp_exact_iff_exact,
        LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_exact_iff_exact]
      have hd₀ : d₀.baseChange B = K₀.subtype.baseChange B ∘ₗ q.baseChange B :=
        LinearMap.baseChange_comp _ _
      rw [hd₀]
      refine hinj_base.comp_exact_iff_exact.mpr ?_
      simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact B hex₁ hq
    · exfalso
      have hbad : (3 : ℕ∞) ≤ 2 :=
        (Nat.cast_le.mpr (by omega : 3 ≤ i + 1 + 2)).trans hi
      exact absurd hbad (by decide)

/-- If `B` is a `2`-pseudoflat commutative `A`-algebra and `M` is stably `2`-pseudocoherent over
`A`, then `B ⊗[A] M` is `2`-pseudocoherent over `B` (Kedlaya–Liu II, Remark 2.4.5). -/
theorem isPseudoCoherentOver_two_baseChange {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [Algebra A B] {M : Type*} [AddCommGroup M]
    [Module A M] (hB : IsPseudoFlat A B 2) (hM : IsStablyPseudoCoherent A M 2) :
    IsPseudoCoherentOver B (B ⊗[A] M) 2 :=
  hB.isPseudoCoherentOver_two_of_le hM le_rfl

end IsPseudoFlat

/-! ### Transitivity of completed rational localisations and Remark 2.4.5 -/

section RatLocTransitivity

open TauCeti.ValuationSpectrum

/-- **Transitivity of completed rational localisations with open numerator ideals** (Wedhorn,
Proposition 8.2 and Remark 8.4). Let `B = A⟨T/s⟩` with `T` generating an open ideal of `A`, and let
`C = B⟨T_B/s_B⟩` with `T_B` generating an open ideal of `B`. Then there exist a finite set `T''` of
`A` generating an open ideal, a denominator `s'' : A`, a proof `hden''` of `HasDenominatorPower`,
and a homeomorphic ring equivalence `e : A⟨T''/s''⟩ ≃+* C` commuting with the canonical maps from
`A`. -/
theorem exists_ratLoc_ringEquiv_ratLoc {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s))
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A))
    (P_B : PairOfDefinition (ratLoc P T s hden)) (T_B : Finset (ratLoc P T s hden))
    (s_B : ratLoc P T s hden)
    (hden_B : P_B.HasDenominatorPower T_B s_B (Localization.Away s_B))
    (hT_B : IsOpen ((Ideal.span (T_B : Set (ratLoc P T s hden)) : Ideal (ratLoc P T s hden)) :
      Set (ratLoc P T s hden))) :
    ∃ (T'' : Finset A) (s'' : A) (hden'' : P.HasDenominatorPower T'' s'' (Localization.Away s'')),
      IsOpen ((Ideal.span (T'' : Set A) : Ideal A) : Set A) ∧
      ∃ e : ratLoc P T'' s'' hden'' ≃+* ratLoc P_B T_B s_B hden_B,
        Continuous e ∧ Continuous e.symm ∧
        ∀ a : A, e (algebraMap A (ratLoc P T'' s'' hden'') a) =
          algebraMap (ratLoc P T s hden) (ratLoc P_B T_B s_B hden_B)
            (algebraMap A (ratLoc P T s hden) a) := by
  classical
  have : IsHuberRing A := ⟨⟨P⟩⟩
  let B := ratLoc P T s hden
  let C := ratLoc P_B T_B s_B hden_B
  -- Step 1: Pull `R(T_B/s_B) ⊆ Spa(B, B⁺)` back to a rational subset of `Spa(A, A⁺)`.
  let Aplus : Subring A := powerBoundedSubring A
  have hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a := fun _ ha ↦ mem_powerBoundedSubring.mp ha
  let Bplus : Subring B := P.completedPlusSubring Aplus T s (Localization.Away s) hden
  have hBplus : ∀ ⦃b : B⦄, b ∈ Bplus → IsPowerBounded b :=
    P.isPowerBounded_of_mem_completedPlusSubring Aplus hAplus T s (Localization.Away s) hden
  let W := spaBasicOpen Bplus T_B s_B
  have hW : W ∈ spaRationalOpens Bplus := spaBasicOpen_mem_spaRationalOpens hT_B
  obtain ⟨V, hV, hVle, hVeq⟩ :=
    exists_mem_spaRationalOpens_locOpensComap_eq P Aplus T s (Localization.Away s) hden hT W hW
  obtain ⟨T', s', hT', rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  -- Step 2: Refine `(T', s')` by `(T, s)` so `iteratedLocalizationRingEquiv` applies.
  let p₀ : P.Presentation := ⟨T, s, hden⟩
  let q₀ : P.Presentation := ⟨T', s', P.hasDenominatorPower_of_isOpen_span T' s' _ hT'⟩
  let p : P.Presentation := p₀.commonRefinement q₀
  have hp_open : IsOpen ((Ideal.span (p.num : Set A) : Ideal A) : Set A) := by
    rw [PairOfDefinition.Presentation.commonRefinement_num]
    exact P.isOpen_span_insert_mul_insert hT hT'
  have hp_basic : spaBasicOpen Aplus p.num p.den = spaBasicOpen Aplus T' s' :=
    (spaBasicOpen_commonRefinement Aplus p₀ q₀).trans (inf_eq_right.mpr hVle)
  obtain ⟨r, hr, hTr⟩ := PairOfDefinition.Presentation.le_def.mp (p₀.le_commonRefinement_left q₀)
  let Q : PairOfDefinition B := P.completionLocalization T s (Localization.Away s) hden
  let ρ : A →+* B := P.toCompletionLoc T s (Localization.Away s) hden
  let TB : Finset B := p.num.image ρ
  let sB' : B := ρ p.den
  have hden_Q : Q.HasDenominatorPower TB sB' (Localization.Away sB') :=
    PairOfDefinition.hasDenominatorPower_completionLocalization_of_coe_eq_image P T s
      (Localization.Away s) hden p.num p.den (Localization.Away p.den) p.hasDenominatorPower
      (Localization.Away sB') TB Finset.coe_image
  let D := ratLoc Q TB sB' hden_Q
  let e₁ : ratLoc P p.num p.den p.hasDenominatorPower ≃+* D :=
    P.iteratedLocalizationRingEquiv T s (Localization.Away s) hden p.num p.den
      (Localization.Away p.den) p.hasDenominatorPower (Localization.Away sB') TB
      Finset.coe_image r hr hTr
  have he₁_cont : Continuous e₁ :=
    P.continuous_iteratedLocalizationRingEquiv T s (Localization.Away s) hden p.num p.den
      (Localization.Away p.den) p.hasDenominatorPower (Localization.Away sB') TB
      Finset.coe_image r hr hTr
  have he₁_symm_cont : Continuous e₁.symm :=
    P.continuous_iteratedLocalizationRingEquiv_symm T s (Localization.Away s) hden p.num p.den
      (Localization.Away p.den) p.hasDenominatorPower (Localization.Away sB') TB
      Finset.coe_image r hr hTr
  have he₁_alg : (e₁ : _ →+* D).comp (P.toCompletionLoc p.num p.den _ p.hasDenominatorPower) =
      (Q.toCompletionLoc TB sB' (Localization.Away sB') hden_Q).comp ρ :=
    P.iteratedLocalizationRingEquiv_coe_comp_toCompletionLoc T s (Localization.Away s) hden
      p.num p.den (Localization.Away p.den) p.hasDenominatorPower (Localization.Away sB') TB
      Finset.coe_image r hr hTr
  -- Step 3: Identify `D = B⟨ρ(p.num)/ρ(p.den)⟩` with `C = B⟨T_B/s_B⟩` by the universal property
  -- of rational localisations, since both cut out the same rational subset of `Spa(B, B⁺)`.
  have hbasic_B : spaBasicOpen Bplus TB sB' = spaBasicOpen Bplus T_B s_B := by
    have hcomap := locOpensComap_spaBasicOpen P Aplus T s (Localization.Away s) hden p.num p.den
    exact hcomap.symm.trans ((congrArg _ hp_basic).trans hVeq)
  have hrat_eq : rationalSubset Bplus TB sB' = rationalSubset Bplus T_B s_B :=
    rationalSubset_eq_of_spaBasicOpen_eq hbasic_B
  obtain ⟨f, ⟨hfc, hfe⟩, -⟩ :=
    existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset Q Bplus TB sB'
      (Localization.Away sB') hden_Q (powerBoundedSubring C)
      ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
      (P_B.continuous_toCompletionLoc T_B s_B (Localization.Away s_B) hden_B).continuousAt
      fun w hw ↦ hrat_eq.ge <| by
        have hle := P_B.completedPlusSubring_le_powerBoundedSubring Bplus hBplus T_B s_B
          (Localization.Away s_B) hden_B
        simpa only [spaComapLoc_val] using
          spaComapLoc_mem_rationalSubset P_B Bplus T_B s_B (Localization.Away s_B) hden_B
            ⟨w, spa_antitone hle hw⟩
  obtain ⟨g, ⟨hgc, hge⟩, -⟩ :=
    existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P_B Bplus T_B s_B
      (Localization.Away s_B) hden_B (powerBoundedSubring D)
      ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
      (Q.continuous_toCompletionLoc TB sB' (Localization.Away sB') hden_Q).continuousAt
      fun w hw ↦ hrat_eq.le <| by
        have hle := Q.completedPlusSubring_le_powerBoundedSubring Bplus hBplus TB sB'
          (Localization.Away sB') hden_Q
        simpa only [spaComapLoc_val] using
          spaComapLoc_mem_rationalSubset Q Bplus TB sB' (Localization.Away sB') hden_Q
            ⟨w, spa_antitone hle hw⟩
  have hgf : g.comp f = RingHom.id D :=
    Q.eq_id_of_comp_toCompletionLoc_eq_self TB sB' (Localization.Away sB') hden_Q (g.comp f)
      (hgc.comp hfc) (by rw [RingHom.comp_assoc, hfe, hge])
  have hfg : f.comp g = RingHom.id C :=
    P_B.eq_id_of_comp_toCompletionLoc_eq_self T_B s_B (Localization.Away s_B) hden_B (f.comp g)
      (hfc.comp hgc) (by rw [RingHom.comp_assoc, hge, hfe])
  let e₂ : D ≃+* C := RingEquiv.ofRingHom f g hfg hgf
  refine ⟨p.num, p.den, p.hasDenominatorPower, hp_open, e₁.trans e₂, hfc.comp he₁_cont,
    he₁_symm_cont.comp hgc, fun a ↦ ?_⟩
  rw [algebraMap_ratLoc, algebraMap_ratLoc, algebraMap_ratLoc]
  have ha₁ := congr($he₁_alg a)
  have ha₂ := congr($hfe (ρ a))
  exact (congrArg f ha₁).trans ha₂

/-- **Analytic half of Kedlaya–Liu II, Remark 2.4.5.** If `M` is stably `m'`-pseudocoherent over
`A`, `B = A⟨T/s⟩` is a completed rational localisation whose numerators span an open ideal, and
`B ⊗[A] M` is `m`-pseudocoherent over `B`, then `B ⊗[A] M` is stably `m`-pseudocoherent over `B`. -/
theorem IsStablyPseudoCoherent.ratLoc_of_isPseudoCoherentOver {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {m m' : ℕ∞} (hM : IsStablyPseudoCoherent A M m') (P : PairOfDefinition A) (T : Finset A)
    (s : A) (hden : P.HasDenominatorPower T s (Localization.Away s))
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A))
    (hcoh : IsPseudoCoherentOver (ratLoc P T s hden) (ratLoc P T s hden ⊗[A] M) m) :
    IsStablyPseudoCoherent (ratLoc P T s hden) (ratLoc P T s hden ⊗[A] M) m := by
  refine ⟨hcoh, fun P_B T_B s_B hden_B hT_B ↦ ?_⟩
  let B := ratLoc P T s hden
  let C := ratLoc P_B T_B s_B hden_B
  -- Express `C = B⟨T_B/s_B⟩` as a single rational localisation `D` of `A`.
  obtain ⟨T'', s'', hden'', hT'', e, he, he_symm, halg⟩ :=
    exists_ratLoc_ringEquiv_ratLoc P T s hden hT P_B T_B s_B hden_B hT_B
  let D := ratLoc P T'' s'' hden''
  have halg_symm (a : A) :
      e.symm (algebraMap B C (algebraMap A B a)) = algebraMap A D a := by
    rw [← halg a, e.symm_apply_apply]
  -- Build mutually inverse `e`- and `e.symm`-semilinear maps `D ⊗[A] M ⇄ C ⊗[B] (B ⊗[A] M)`
  -- via `TensorProduct.liftAddHom` so no auxiliary `Algebra A C` instance is introduced.
  let fwdBilin : D →+ M →+ C ⊗[B] (B ⊗[A] M) :=
    AddMonoidHom.mk' (fun d ↦ AddMonoidHom.mk' (fun x ↦ e d ⊗ₜ[B] ((1 : B) ⊗ₜ[A] x))
      fun x y ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
      fun d₁ d₂ ↦ AddMonoidHom.ext fun x ↦ by simp [map_add, TensorProduct.add_tmul]
  let fwdAdd : D ⊗[A] M →+ C ⊗[B] (B ⊗[A] M) :=
    TensorProduct.liftAddHom fwdBilin fun a d x ↦ by
      dsimp [fwdBilin]
      calc e (a • d) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] x)
          = (algebraMap A B a • e d) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] x) := by
              rw [Algebra.smul_def, map_mul, halg a, Algebra.smul_def]
        _ = e d ⊗ₜ[B] (algebraMap A B a • ((1 : B) ⊗ₜ[A] x)) :=
              TensorProduct.smul_tmul (algebraMap A B a) (e d) _
        _ = e d ⊗ₜ[B] ((a • (1 : B)) ⊗ₜ[A] x) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def]
        _ = e d ⊗ₜ[B] ((1 : B) ⊗ₜ[A] (a • x)) := by
              rw [TensorProduct.smul_tmul]
  let bwdInner (c : C) : B ⊗[A] M →+ D ⊗[A] M :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b ↦ AddMonoidHom.mk'
        (fun x ↦ (e.symm c * e.symm (algebraMap B C b)) ⊗ₜ[A] x)
        fun x y ↦ TensorProduct.tmul_add _ x y)
        fun b₁ b₂ ↦ AddMonoidHom.ext fun x ↦ by
          simp [map_add, mul_add, TensorProduct.add_tmul])
      fun a b x ↦ by
        simp only [AddMonoidHom.mk'_apply]
        rw [Algebra.smul_def, map_mul, map_mul, halg_symm a, ← mul_assoc,
          mul_comm (e.symm c), mul_assoc, ← Algebra.smul_def, TensorProduct.smul_tmul]
  have hbwdInner (c : C) (b : B) (x : M) :
      bwdInner c (b ⊗ₜ[A] x) = (e.symm c * e.symm (algebraMap B C b)) ⊗ₜ[A] x := by
    simp [bwdInner]
  let bwdBilin : C →+ (B ⊗[A] M) →+ D ⊗[A] M :=
    AddMonoidHom.mk' bwdInner fun c₁ c₂ ↦ AddMonoidHom.ext fun z ↦ by
      rw [AddMonoidHom.add_apply]
      induction z using TensorProduct.inductionOn with
      | tmul b x =>
        rw [hbwdInner, hbwdInner, hbwdInner, map_add, add_mul, TensorProduct.add_tmul]
      | add z₁ z₂ ih₁ ih₂ =>
        rw [map_add, map_add, map_add, ih₁, ih₂]
        abel
  let bwdAdd : C ⊗[B] (B ⊗[A] M) →+ D ⊗[A] M :=
    TensorProduct.liftAddHom bwdBilin fun b c z ↦ by
      simp only [bwdBilin, AddMonoidHom.mk'_apply]
      induction z using TensorProduct.inductionOn with
      | tmul b' x =>
        rw [TensorProduct.smul_tmul', hbwdInner, hbwdInner]
        congr 1
        rw [Algebra.smul_def, smul_eq_mul, map_mul, map_mul, map_mul]
        ring
      | add z₁ z₂ ih₁ ih₂ =>
        rw [smul_add, map_add, map_add, ih₁, ih₂]
  have hfwdAdd (d : D) (x : M) : fwdAdd (d ⊗ₜ[A] x) = e d ⊗ₜ[B] ((1 : B) ⊗ₜ[A] x) := by
    simp [fwdAdd, fwdBilin]
  have hbwdAdd (c : C) (b : B) (x : M) :
      bwdAdd (c ⊗ₜ[B] (b ⊗ₜ[A] x)) = (e.symm c * e.symm (algebraMap B C b)) ⊗ₜ[A] x := by
    simp [bwdAdd, bwdBilin, hbwdInner]
  let fwdₛ : D ⊗[A] M →ₛₗ[(e : D →+* C)] C ⊗[B] (B ⊗[A] M) :=
    { toFun := fwdAdd
      map_add' := map_add fwdAdd
      map_smul' := fun d z ↦ by
        simp only [RingHom.coe_coe]
        induction z using TensorProduct.inductionOn with
        | tmul d' x =>
          rw [TensorProduct.smul_tmul', smul_eq_mul, hfwdAdd, hfwdAdd, map_mul,
            TensorProduct.smul_tmul', smul_eq_mul]
        | add z₁ z₂ ih₁ ih₂ => simp [smul_add, map_add, ih₁, ih₂] }
  let bwdₛ : C ⊗[B] (B ⊗[A] M) →ₛₗ[(e.symm : C →+* D)] D ⊗[A] M :=
    { toFun := bwdAdd
      map_add' := map_add bwdAdd
      map_smul' := fun c z ↦ by
        simp only [RingHom.coe_coe]
        induction z using TensorProduct.inductionOn with
        | tmul c' w =>
          induction w using TensorProduct.inductionOn with
          | tmul b x =>
            rw [TensorProduct.smul_tmul', smul_eq_mul, hbwdAdd, hbwdAdd, map_mul, mul_assoc,
              TensorProduct.smul_tmul', smul_eq_mul]
          | add w₁ w₂ ih₁ ih₂ =>
            rw [TensorProduct.tmul_add, smul_add, map_add, map_add, smul_add, ih₁, ih₂]
        | add z₁ z₂ ih₁ ih₂ => simp [smul_add, map_add, ih₁, ih₂] }
  have hfwdₛ (z : D ⊗[A] M) : fwdₛ z = fwdAdd z := rfl
  have hbwdₛ (w : C ⊗[B] (B ⊗[A] M)) : bwdₛ w = bwdAdd w := rfl
  -- Transport natural completeness from `D ⊗[A] M` to `C ⊗[B] (B ⊗[A] M)`.
  refine (hM.isNaturallyComplete_tensor P T'' s'' hden'' hT'').of_semilinear
    he he_symm fwdₛ bwdₛ (fun z ↦ ?_) (fun z ↦ ?_)
  · induction z using TensorProduct.inductionOn with
    | tmul d x =>
      rw [hfwdₛ, hfwdAdd, hbwdₛ, hbwdAdd, e.symm_apply_apply, map_one, map_one, mul_one]
    | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  · induction z using TensorProduct.inductionOn with
    | tmul c w =>
      induction w using TensorProduct.inductionOn with
      | tmul b x =>
        rw [hbwdₛ, hbwdAdd, hfwdₛ, hfwdAdd, map_mul, e.apply_symm_apply, e.apply_symm_apply,
          mul_comm c, ← Algebra.smul_def, TensorProduct.smul_tmul, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
      | add w₁ w₂ ih₁ ih₂ =>
        rw [TensorProduct.tmul_add, map_add, map_add, ih₁, ih₂]
    | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]

/-- **Base change of stable `2`-pseudocoherence along a `2`-pseudoflat rational localisation**
(Kedlaya–Liu II, Remark 2.4.5). If `A⟨T/s⟩` is `2`-pseudoflat over `A` and `M` is stably
`2`-pseudocoherent over `A`, then `A⟨T/s⟩ ⊗[A] M` is stably `2`-pseudocoherent over `A⟨T/s⟩`. -/
theorem IsStablyPseudoCoherent.ratLoc_two {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (hM : IsStablyPseudoCoherent A M 2) (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s))
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A))
    (hflat : IsPseudoFlat A (ratLoc P T s hden) 2) :
    IsStablyPseudoCoherent (ratLoc P T s hden) (ratLoc P T s hden ⊗[A] M) 2 :=
  hM.ratLoc_of_isPseudoCoherentOver P T s hden hT (hflat.isPseudoCoherentOver_two_baseChange hM)

/-- **Composition of pseudoflatness along scalar extensions preserving stable pseudocoherence**
(Kedlaya–Liu II, Remark 2.4.5). If `B` is an `m`-pseudoflat commutative `A`-algebra such that base
change to `B` sends stably `m`-pseudocoherent `A`-modules to stably `m'`-pseudocoherent
`B`-modules, and `C` is an `m'`-pseudoflat `B`-module, then `C` is `m`-pseudoflat over `A`. -/
theorem IsPseudoFlat.comp_of_forall_baseChange {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra A B] {C : Type*} [AddCommGroup C] [Module A C] [Module B C] [IsScalarTower A B C]
    {m m' : ℕ∞} (hAB : IsPseudoFlat A B m)
    (hstab : ∀ (n : ℕ) (K : Submodule A (Fin n → A)),
      IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m →
      IsStablyPseudoCoherent B (B ⊗[A] ((Fin n → A) ⧸ K)) m')
    (hBC : IsPseudoFlat B C m') : IsPseudoFlat A C m := by
  classical
  intro n K hK
  have hinj_B : Function.Injective (K.subtype.baseChange B) :=
    IsPseudoFlat.injective_baseChange_of_injective_rTensor (hAB n K hK)
  have hsurj_B : Function.Surjective (K.mkQ.baseChange B) :=
    K.mkQ.baseChange_surjective B (Submodule.mkQ_surjective K)
  have hex_B : Function.Exact (K.subtype.baseChange B) (K.mkQ.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using
      lTensor_exact B (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K)
  have : Module.Finite B (B ⊗[A] (Fin n → A)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight A B B (Fin n)).symm
  have : Module.Projective B (B ⊗[A] (Fin n → A)) :=
    Module.Projective.of_equiv (TensorProduct.piScalarRight A B B (Fin n)).symm
  have hinj_BC : Function.Injective ((K.subtype.baseChange B).rTensor C) :=
    hBC.rTensor_injective hinj_B hsurj_B hex_B (hstab n K hK)
  let cancelK : (B ⊗[A] K) ⊗[B] C ≃ₗ[A] K ⊗[A] C :=
    (TensorProduct.comm B (B ⊗[A] K) C).restrictScalars A ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C K).restrictScalars A ≪≫ₗ
      TensorProduct.comm A C K
  let cancelF : (B ⊗[A] (Fin n → A)) ⊗[B] C ≃ₗ[A] (Fin n → A) ⊗[A] C :=
    (TensorProduct.comm B (B ⊗[A] (Fin n → A)) C).restrictScalars A ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C (Fin n → A)).restrictScalars A ≪≫ₗ
      TensorProduct.comm A C (Fin n → A)
  have hnat : cancelF.toLinearMap ∘ₗ ((K.subtype.baseChange B).rTensor C).restrictScalars A =
      K.subtype.rTensor C ∘ₗ cancelK.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x c =>
      induction x using TensorProduct.inductionOn with
      | tmul b k => simp [cancelK, cancelF]
      | add x₁ x₂ ih₁ ih₂ => simp [TensorProduct.add_tmul, map_add, ih₁, ih₂]
    | add z₁ z₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  have hinj_comp : Function.Injective (K.subtype.rTensor C ∘ₗ cancelK.toLinearMap) := by
    rw [← hnat]
    exact cancelF.injective.comp hinj_BC
  intro z₁ z₂ hz
  apply cancelK.symm.injective
  apply hinj_comp
  simpa [LinearMap.comp_apply] using hz

/-- **Composition of `2`-pseudoflatness along a `2`-pseudoflat rational localisation**
(Kedlaya–Liu II, Remark 2.4.5). -/
theorem IsPseudoFlat.comp_ratLoc {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s))
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A))
    {C : Type*} [AddCommGroup C] [Module A C] [Module (ratLoc P T s hden) C]
    [IsScalarTower A (ratLoc P T s hden) C]
    (hAB : IsPseudoFlat A (ratLoc P T s hden) 2)
    (hBC : IsPseudoFlat (ratLoc P T s hden) C 2) : IsPseudoFlat A C 2 :=
  hAB.comp_of_forall_baseChange (fun _ _ hK ↦ hK.ratLoc_two P T s hden hT hAB) hBC

end RatLocTransitivity

/-! ### Principal quotients are not pseudoflat -/

section NonExample

/-- **A quotient `A ⧸ (f)` by a non-unit regular element is not `m`-pseudoflat** whenever it is
stably `m`-pseudocoherent: `Tor₁^A(A ⧸ (f), A ⧸ (f)) ≃ A ⧸ (f)` is nonzero. -/
theorem not_isPseudoFlat_quotient_span_singleton {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {f : A} {m : ℕ∞} (hf_reg : IsSMulRegular A f) (hf_unit : ¬ IsUnit f)
    (hstab : IsStablyPseudoCoherent A (A ⧸ Ideal.span {f}) m) :
    ¬ IsPseudoFlat A (A ⧸ Ideal.span {f}) m := by
  intro hflat
  set I : Ideal A := Ideal.span {f}
  set Q := A ⧸ I
  let mul_f : A →ₗ[A] I :=
    { toFun := fun a ↦ ⟨a * f, Ideal.mem_span_singleton.mpr ⟨a, mul_comm a f⟩⟩
      map_add' := fun a b ↦ Subtype.ext (add_mul a b f)
      map_smul' := fun r a ↦ Subtype.ext (mul_assoc r a f) }
  have hmul_inj : Function.Injective mul_f := fun a b hab ↦ by
    have hEq : a * f = b * f := congrArg Subtype.val hab
    rw [mul_comm a f, mul_comm b f] at hEq
    exact hf_reg hEq
  have hmul_surj : Function.Surjective mul_f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨a, Subtype.ext (mul_comm a f)⟩
  let eI : A ≃ₗ[A] I := LinearEquiv.ofBijective mul_f ⟨hmul_inj, hmul_surj⟩
  have hinj : Function.Injective (I.subtype.rTensor Q) :=
    hflat.rTensor_injective I.injective_subtype (Submodule.mkQ_surjective I)
      (LinearMap.exact_subtype_mkQ I) hstab
  let z : I ⊗[A] Q := eI 1 ⊗ₜ[A] Submodule.Quotient.mk 1
  have hf0 : f • (Submodule.Quotient.mk (p := I) (1 : A)) = 0 := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
    exact Ideal.subset_span (Set.mem_singleton f)
  have hz_zero : I.subtype.rTensor Q z = 0 := by
    calc I.subtype.rTensor Q z
        = (1 * f : A) ⊗ₜ[A] Submodule.Quotient.mk (p := I) 1 := rfl
      _ = (f • (1 : A)) ⊗ₜ[A] Submodule.Quotient.mk (p := I) 1 := by
          rw [one_mul, smul_eq_mul, mul_one]
      _ = (1 : A) ⊗ₜ[A] (f • Submodule.Quotient.mk (p := I) 1) :=
          TensorProduct.smul_tmul f 1 _
      _ = 0 := by rw [hf0, TensorProduct.tmul_zero]
  have hz : z = 0 := hinj (hz_zero.trans (map_zero _).symm)
  let proj : I ⊗[A] Q →ₗ[A] Q :=
    (TensorProduct.lid A Q).toLinearMap ∘ₗ LinearMap.rTensor Q eI.symm.toLinearMap
  have hproj : proj z = Submodule.Quotient.mk 1 := by
    simp [proj, z]
  rw [hz, map_zero] at hproj
  have hmem : (1 : A) ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hproj.symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  exact hf_unit ⟨⟨f, c, hc.symm, mul_comm c f ▸ hc.symm⟩, rfl⟩

end NonExample

end TauCeti.Huber
