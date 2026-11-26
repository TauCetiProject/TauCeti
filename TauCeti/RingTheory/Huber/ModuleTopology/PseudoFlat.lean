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
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# Pseudoflat modules and base change of stable pseudocoherence

Let `A` be a topological commutative ring and `m ∈ ℕ ∪ {∞}`. An `A`-module `B` is *`m`-pseudoflat*
over `A` (Kedlaya–Liu II, Definition 2.4.4) if `Tor₁^A(Q, B) = 0` for every stably
`m`-pseudocoherent `A`-module `Q`, i.e. `K ⊗[A] B → (Fin n → A) ⊗[A] B` is injective whenever
`(Fin n → A) ⧸ K` is stably `m`-pseudocoherent over `A`. When `B` is a `2`-pseudoflat commutative
`A`-algebra, base change sends stably `2`-pseudocoherent `A`-modules to `2`-pseudocoherent
`B`-modules (`IsPseudoFlat.isPseudoCoherentOver_two_baseChange`); combining with
`IsStablyPseudoCoherent.ratLoc_of_isPseudoCoherentOver` gives Kedlaya–Liu II, Remark 2.4.5
(`IsStablyPseudoCoherent.ratLoc_two` and `IsPseudoFlat.comp_ratLoc`).

## Main definitions and results

* `TauCeti.Huber.IsPseudoFlat A B m`: the `A`-module `B` is `m`-pseudoflat over `A`.
* `TauCeti.Huber.IsPseudoFlat.mono`, `of_flat`, `of_equiv`, `of_retract`, `prod`,
  `rTensor_injective`, `isPseudoFlat_iff_injective_rTensor`: permanence and projective presentation
  characterisation.
* `TauCeti.Huber.IsPseudoFlat.isPseudoCoherentOver_two_baseChange`,
  `TauCeti.Huber.IsStablyPseudoCoherent.ratLoc_two`, `comp_of_forall_baseChange`, and `comp_ratLoc`:
  Remark 2.4.5 base change and composition.
* `TauCeti.Huber.not_isPseudoFlat_quotient_span_singleton`: non-pseudoflatness of `A ⧸ (f)`.

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
    IsPseudoFlat A B m ↔ ∀ (n : ℕ) (K : Submodule A (Fin n → A)),
      IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m → Function.Injective (K.subtype.rTensor B) :=
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
    (hri : r ∘ₗ i = LinearMap.id) (h : IsPseudoFlat A B m) : IsPseudoFlat A B' m :=
  fun n K hK ↦ K.subtype.injective_rTensor_of_comp_eq_id hri (h n K hK)

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
  let p₁ := LinearMap.fst A B B'; let p₂ := LinearMap.snd A B B'
  have hsq₁ : K.subtype.rTensor B ∘ₗ LinearMap.lTensor K p₁ =
      LinearMap.lTensor (Fin n → A) p₁ ∘ₗ K.subtype.rTensor (B × B') := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hsq₂ : K.subtype.rTensor B' ∘ₗ LinearMap.lTensor K p₂ =
      LinearMap.lTensor (Fin n → A) p₂ ∘ₗ K.subtype.rTensor (B × B') := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hz₁ : LinearMap.lTensor K p₁ z = 0 := (h₁ n K hK) <| by
    rw [← LinearMap.comp_apply, hsq₁, LinearMap.comp_apply, hz₀, map_zero, map_zero]
  have hz₂ : LinearMap.lTensor K p₂ z = 0 := (h₂ n K hK) <| by
    rw [← LinearMap.comp_apply, hsq₂, LinearMap.comp_apply, hz₀, map_zero, map_zero]
  have hid : LinearMap.inl A B B' ∘ₗ p₁ + LinearMap.inr A B B' ∘ₗ p₂ = LinearMap.id := by
    ext x <;> simp [p₁, p₂]
  calc z = LinearMap.lTensor K (LinearMap.inl A B B' ∘ₗ p₁ + LinearMap.inr A B B' ∘ₗ p₂) z := by
          rw [hid, LinearMap.lTensor_id, LinearMap.id_apply]
    _ = 0 := by
          rw [LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp,
            LinearMap.lTensor_comp]
          simp [hz₁, hz₂]

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
  set K : Submodule A (Fin n → A) := LinearMap.ker (p ∘ₗ f)
  have hK : IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m :=
    hP.of_equiv ((p ∘ₗ f).quotKerEquivOfSurjective (hp.comp hf)).symm
  let gK : M →ₗ[A] K := (g ∘ₗ i).codRestrict K fun x ↦ by
    have hfg_i : f (g (i x)) = i x := congr($hfg (i x))
    simp [K, hfg_i, hexact.apply_apply_eq_zero x]
  have hrange : ∀ k : K, f k.1 ∈ LinearMap.range i := fun k ↦ (hexact (f k.1)).mp k.2
  let fK : K →ₗ[A] M :=
    (LinearEquiv.ofInjective i hi).symm.toLinearMap ∘ₗ (f ∘ₗ K.subtype).codRestrict _ hrange
  have hfKgK : fK.rTensor B ∘ₗ gK.rTensor B = LinearMap.id := by
    rw [← LinearMap.rTensor_comp]
    suffices fK ∘ₗ gK = LinearMap.id by rw [this, LinearMap.rTensor_id]
    ext x; apply hi; dsimp [fK, gK]
    exact (congrArg Subtype.val ((LinearEquiv.ofInjective i hi).apply_symm_apply _)).trans
      congr($hfg (i x))
  have hcomp : g.rTensor B ∘ₗ i.rTensor B = K.subtype.rTensor B ∘ₗ gK.rTensor B := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, LinearMap.subtype_comp_codRestrict]
  exact Function.Injective.of_comp (f := g.rTensor B) <| by
    rw [← LinearMap.coe_comp, hcomp]
    exact (hB n K hK).comp (Function.LeftInverse.injective fun z ↦ congr($hfKgK z))

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

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {B : Type*} [CommRing B] [Algebra A B] {M : Type*} [AddCommGroup M] [Module A M]

/-- **Algebraic half of Kedlaya–Liu II, Remark 2.4.5.** If `B` is an `m`-pseudoflat commutative
`A`-algebra with `2 ≤ m` and `M` is stably `m`-pseudocoherent over `A`, then `B ⊗[A] M` is
`2`-pseudocoherent over `B`. -/
theorem isPseudoCoherentOver_two_of_le {m : ℕ∞} (hB : IsPseudoFlat A B m)
    (hM : IsStablyPseudoCoherent A M m) (hm : 2 ≤ m) : IsPseudoCoherentOver B (B ⊗[A] M) 2 := by
  classical
  obtain ⟨n₀, ε, hε, hK₀⟩ := IsPseudoCoherentOver.succ_iff.mp
    (hM.isPseudoCoherentOver.mono hm : IsPseudoCoherentOver A M ((1 : ℕ∞) + 1))
  set K₀ := LinearMap.ker ε
  have hinj_base : Function.Injective (K₀.subtype.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using
      (K₀.subtype.lTensor_inj_iff_rTensor_inj B).2
        (hB n₀ K₀ (hM.of_equiv (ε.quotKerEquivOfSurjective hε).symm))
  obtain ⟨n₁, q, hq, hK₁⟩ :=
    IsPseudoCoherentOver.succ_iff.mp (by simpa using hK₀ : IsPseudoCoherentOver A K₀ ((0 : ℕ∞) + 1))
  have := IsPseudoCoherentOver.zero_iff.mp hK₁
  obtain ⟨n₂, r, hr⟩ := Module.Finite.exists_fin' A (LinearMap.ker q)
  let d₀ : (Fin n₁ → A) →ₗ[A] (Fin n₀ → A) := K₀.subtype ∘ₗ q
  let d₁ : (Fin n₂ → A) →ₗ[A] (Fin n₁ → A) := (LinearMap.ker q).subtype ∘ₗ r
  have hex₀ : Function.Exact d₀ ε :=
    hq.comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map ε)
  have hex₁ : Function.Exact d₁ q :=
    hr.comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map q)
  let e (k : ℕ) := TensorProduct.piScalarRight A B B (Fin k)
  let rk : ℕ → ℕ | 0 => n₀ | 1 => n₁ | 2 => n₂ | _ + 3 => 0
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
      dsimp only [d₀]; rw [LinearMap.baseChange_comp q K₀.subtype]
      refine hinj_base.comp_exact_iff_exact.mpr ?_
      simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact B hex₁ hq
    · exact absurd ((Nat.cast_le.mpr (by omega : 3 ≤ i + 1 + 2)).trans hi) (by decide)

/-- If `B` is a `2`-pseudoflat commutative `A`-algebra and `M` is stably `2`-pseudocoherent over
`A`, then `B ⊗[A] M` is `2`-pseudocoherent over `B` (Kedlaya–Liu II, Remark 2.4.5). -/
theorem isPseudoCoherentOver_two_baseChange (hB : IsPseudoFlat A B 2)
    (hM : IsStablyPseudoCoherent A M 2) : IsPseudoCoherentOver B (B ⊗[A] M) 2 :=
  hB.isPseudoCoherentOver_two_of_le hM le_rfl

end IsPseudoFlat

/-! ### Rational-localisation base change and Remark 2.4.5 -/

section RatLocTransitivity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Base change of stable `2`-pseudocoherence along a `2`-pseudoflat rational localisation**
(Kedlaya–Liu II, Remark 2.4.5). If `A⟨T/s⟩` is `2`-pseudoflat over `A` and `M` is stably
`2`-pseudocoherent over `A`, then `A⟨T/s⟩ ⊗[A] M` is stably `2`-pseudocoherent over `A⟨T/s⟩`. -/
theorem IsStablyPseudoCoherent.ratLoc_two {M : Type*} [AddCommGroup M] [Module A M]
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
theorem IsPseudoFlat.comp_of_forall_baseChange {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] {C : Type*} [AddCommGroup C] [Module A C] [Module B C]
    [IsScalarTower A B C] {m m' : ℕ∞} (hAB : IsPseudoFlat A B m)
    (hstab : ∀ (n : ℕ) (K : Submodule A (Fin n → A)),
      IsStablyPseudoCoherent A ((Fin n → A) ⧸ K) m →
      IsStablyPseudoCoherent B (B ⊗[A] ((Fin n → A) ⧸ K)) m')
    (hBC : IsPseudoFlat B C m') : IsPseudoFlat A C m := by
  classical
  intro n K hK
  have hinj_B : Function.Injective (K.subtype.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using
      (K.subtype.lTensor_inj_iff_rTensor_inj B).2 (hAB n K hK)
  have hex_B : Function.Exact (K.subtype.baseChange B) (K.mkQ.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using
      lTensor_exact B (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K)
  have := Module.Finite.equiv (TensorProduct.piScalarRight A B B (Fin n)).symm
  have := Module.Projective.of_equiv (TensorProduct.piScalarRight A B B (Fin n)).symm
  have hinj_BC := hBC.rTensor_injective hinj_B
    (K.mkQ.baseChange_surjective B (Submodule.mkQ_surjective K)) hex_B (hstab n K hK)
  let cancelK := TensorProduct.cancelBaseChangeLeft A B K C
  let cancelF := TensorProduct.cancelBaseChangeLeft A B (Fin n → A) C
  have hnat : cancelF.toLinearMap ∘ₗ ((K.subtype.baseChange B).rTensor C).restrictScalars A =
      K.subtype.rTensor C ∘ₗ cancelK.toLinearMap := LinearMap.ext fun z ↦ by
    induction z with
    | tmul x c => induction x with
      | tmul b k => simp [cancelK, cancelF]
      | add _ _ _ _ => simp_all [TensorProduct.add_tmul]
    | add _ _ _ _ => simp_all
  have hinj_comp : Function.Injective (K.subtype.rTensor C ∘ₗ cancelK.toLinearMap) :=
    hnat ▸ cancelF.injective.comp hinj_BC
  exact fun z₁ z₂ hz ↦ cancelK.symm.injective <| hinj_comp <| by simpa using hz

/-- **Composition of `2`-pseudoflatness along a `2`-pseudoflat rational localisation**
(Kedlaya–Liu II, Remark 2.4.5). -/
theorem IsPseudoFlat.comp_ratLoc (P : PairOfDefinition A) (T : Finset A) (s : A)
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
  set I : Ideal A := Ideal.span {f}; set Q := A ⧸ I
  let mul_f : A →ₗ[A] I :=
    { toFun a := ⟨a * f, Ideal.mem_span_singleton.mpr ⟨a, mul_comm a f⟩⟩
      map_add' a b := Subtype.ext (add_mul a b f)
      map_smul' r a := Subtype.ext (mul_assoc r a f) }
  let eI : A ≃ₗ[A] I := LinearEquiv.ofBijective mul_f
    ⟨fun a b hab ↦ hf_reg (by simpa [mul_f, mul_comm] using congrArg Subtype.val hab),
      fun ⟨_, hx⟩ ↦ let ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx
        ⟨a, Subtype.ext (ha ▸ mul_comm a f)⟩⟩
  have hinj := hflat.rTensor_injective I.injective_subtype (Submodule.mkQ_surjective I)
    (LinearMap.exact_subtype_mkQ I) hstab
  let z : I ⊗[A] Q := eI 1 ⊗ₜ[A] Submodule.Quotient.mk 1
  have hz_zero : I.subtype.rTensor Q z = 0 := by
    have hf0 : f • (Submodule.Quotient.mk (p := I) (1 : A)) = 0 := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
      exact Ideal.subset_span (Set.mem_singleton f)
    calc I.subtype.rTensor Q z = (1 * f : A) ⊗ₜ[A] Submodule.Quotient.mk (p := I) 1 := rfl
      _ = (f • (1 : A)) ⊗ₜ[A] Submodule.Quotient.mk (p := I) 1 := by
        rw [one_mul, smul_eq_mul, mul_one]
      _ = 0 := by rw [TensorProduct.smul_tmul, hf0, TensorProduct.tmul_zero]
  have hz : z = 0 := hinj (hz_zero.trans (map_zero _).symm)
  have hproj : ((TensorProduct.lid A Q).toLinearMap ∘ₗ
      LinearMap.rTensor Q eI.symm.toLinearMap) z = Submodule.Quotient.mk 1 := by simp [z]
  rw [hz, map_zero] at hproj
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero I).mp hproj.symm)
  exact hf_unit ⟨⟨f, c, hc.symm, mul_comm c f ▸ hc.symm⟩, rfl⟩

end NonExample

end TauCeti.Huber
