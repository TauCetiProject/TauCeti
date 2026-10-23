/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Limit
public import TauCeti.Algebra.Homology.AInfinity.Algebra.IntrinsicFormality
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction

/-!
# Kadeishvili's intrinsic formality criterion

Let `ℋ` be a graded algebra, presented as a minimal `A∞` algebra without operations above arity
two.  Its Hochschild differential raises the arity of a cochain concentrated in one arity by one
(`TauCeti.AInfinityAlgebra.hochschildDifferential_comp_lengthProj`), so its Hochschild cohomology
is bigraded by arity and internal degree.  An arity-`n` cochain of suspended degree one, the degree
of the Taylor component of an operation `mₙ`, has internal degree `2 - n`.  The bigraded piece
`HH^{n, 2 - n}(H, H)` vanishes when every Hochschild cocycle of `ℋ` of suspended degree one
concentrated on the words of length `n` is the Hochschild differential of a cochain of suspended
degree zero concentrated on the words of length `n - 1`.

**Kadeishvili's criterion.**  If `HH^{n, 2 - n}(H, H)` vanishes for every `n ≥ 3`, then every
minimal `A∞` structure on `H` with the grading and the binary operation of `ℋ` is `A∞` isomorphic
to `ℋ`, over any commutative ring
(`TauCeti.AInfinityAlgebra.IsMinimal.exists_isIso_of_forall_hochschildVanishesAt`).  Over a
field `ℋ` is therefore intrinsically formal
(`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt`): every
`A∞` algebra whose cohomology algebra is isomorphic to `ℋ` is formal.  The criterion is sufficient,
not necessary.

The proof kills the higher operations one arity at a time.  If a minimal structure `𝒜` agrees with
`ℋ` on the words of length at most `n ≥ 2`, its obstruction in arity `n + 1` is a Hochschild
cocycle of `ℋ` (`TauCeti.AInfinityAlgebra.hochschildDifferential_obstruction`).  By hypothesis it
bounds a cochain of arity `n`, and the gauge transformation of `𝒜` by the negative of that cochain
agrees with `ℋ` on the words of length at most `n + 1`
(`TauCeti.AInfinityAlgebra.IsMinimal.taylor_gauge_apply_eq_of_hochschildDifferential`).  The gauge
morphism is the identity on the words of length less than `n`, so the composites of the successive
gauge morphisms stabilise, and their limit (`TauCeti.AInfinityHom.limit`) is an `A∞` isomorphism
from `ℋ` to the original structure.

## Main results

* `TauCeti.AInfinityAlgebra.HochschildVanishesAt`: the vanishing of the bigraded Hochschild
  cohomology `HH^{n, 2 - n}(H, H)`, stated on cochains.
* `TauCeti.AInfinityAlgebra.IsMinimal.exists_isIso_of_forall_hochschildVanishesAt`: if
  `HH^{n, 2 - n}(H, H) = 0` for every `n ≥ 3`, every minimal `A∞` structure with the grading and the
  binary operation of `ℋ` is `A∞` isomorphic to `ℋ`.
* `TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt`: over a
  field, such a graded algebra is intrinsically formal.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
-/

public section

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

universe uR uK uA

section CommRing

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {ℋ ℬ : AInfinityAlgebra R A}

variable (ℋ) in
/-- The bigraded Hochschild cohomology `HH^{n, 2 - n}(H, H)` of `ℋ` vanishes: every Hochschild
cocycle of `ℋ` of suspended degree one concentrated on the words of length `n` is the Hochschild
differential of a cochain of suspended degree zero concentrated on the words of length `n - 1`.
This is the obstruction group for killing the operation of arity `n`. -/
def HochschildVanishesAt (n : {n : ℕ // 1 < n}) : Prop :=
  ∀ F : ReducedTensorWords R A →ₗ[R] A,
    LinearMap.IsHomogeneous F (gradedPiece (ℋ.grading.shift 1)) (ℋ.grading.shift 1).piece 1 →
    F ∘ₗ lengthProj R A ⟨n.1, by omega⟩ = F → ℋ.hochschildDifferential 1 F = 0 →
    ∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      φ ∘ₗ lengthProj R A ⟨n.1 - 1, by omega⟩ = φ ∧ ℋ.hochschildDifferential 0 φ = F

/-- Unfolding `HochschildVanishesAt`. -/
theorem hochschildVanishesAt_iff {n : {n : ℕ // 1 < n}} :
    ℋ.HochschildVanishesAt n ↔ ∀ F : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous F (gradedPiece (ℋ.grading.shift 1)) (ℋ.grading.shift 1).piece 1 →
      F ∘ₗ lengthProj R A ⟨n.1, by omega⟩ = F → ℋ.hochschildDifferential 1 F = 0 →
      ∃ φ : ReducedTensorWords R A →ₗ[R] A,
        LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
          (ℋ.grading.shift 1).piece 0 ∧
        φ ∘ₗ lengthProj R A ⟨n.1 - 1, by omega⟩ = φ ∧ ℋ.hochschildDifferential 0 φ = F :=
  Iff.rfl

/-- A stage of the killing procedure: a minimal `A∞` structure with the grading of `ℋ` whose
Taylor map agrees with that of `ℋ` on the words of length at most `N`, with an `A∞` morphism to
`ℬ` whose linear part is the identity. -/
private structure KillingStage (ℋ ℬ : AInfinityAlgebra R A) (N : ℕ) where
  /-- The current `A∞` structure. -/
  alg : AInfinityAlgebra R A
  grading_eq : alg.grading = ℋ.grading
  isMinimal : alg.IsMinimal
  taylor_eq : ∀ z ∈ filtration R A N, alg.taylor z = ℋ.taylor z
  /-- The comparison morphism to `ℬ`. -/
  hom : AInfinityHom alg ℬ
  linearPart_hom : hom.linearPart = LinearMap.id

/-- **The killing step.**  If the bigraded Hochschild cohomology of `ℋ` vanishes in arity `k + 3`,
a stage agreeing with `ℋ` on the words of length at most `k + 2` is followed by one agreeing with
`ℋ` on the words of length at most `k + 3`, whose comparison morphism has the same Taylor
components on the words of length at most `k + 1`. -/
private theorem exists_killingStage_succ (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    {k : ℕ}
    (hHH : ℋ.HochschildVanishesAt ⟨k + 3, by omega⟩)
    (s : KillingStage ℋ ℬ (k + 2)) :
    ∃ s' : KillingStage ℋ ℬ (k + 3),
      ∀ z ∈ filtration R A (k + 1), s'.hom.taylor z = s.hom.taylor z := by
  -- The obstruction in arity `k + 3` bounds a cochain `ψ` of arity `k + 2`.
  obtain ⟨ψ, hψ, hψk, hδψ⟩ := hHH (s.alg.obstruction ℋ ⟨k + 3, by omega⟩)
    (isHomogeneous_obstruction s.grading_eq _) (obstruction_comp_lengthProj _ _ _)
    (hochschildDifferential_obstruction hℋ hm s.grading_eq (by omega) s.taylor_eq)
  -- The gauge transformation by `φ = -ψ` removes it.
  have hφ : LinearMap.IsHomogeneous (-ψ) (gradedPiece (s.alg.grading.shift 1))
      (s.alg.grading.shift 1).piece 0 := by
    rw [s.grading_eq]
    exact hψ.neg
  have hφe : ∀ z ∈ filtration R A (k + 1), (-ψ) z = 0 := fun z hz ↦ by
    rw [LinearMap.neg_apply, ← hψk, LinearMap.comp_apply,
      lengthProj_apply_eq_zero_of_mem_filtration R A (by dsimp only; omega) hz, map_zero, neg_zero]
  have hφ₁ : (-ψ) ∘ₗ ofLetter R A = 0 := LinearMap.ext fun a ↦
    hφe _ (filtration_monotone R A (by omega) (ofLetter_mem_filtration R A a))
  have hδ : ∀ z ∈ filtration R A (k + 1 + 2),
      ℋ.hochschildDifferential 0 (-ψ) z = ℋ.taylor z - s.alg.taylor z := fun z hz ↦ by
    rw [← neg_one_smul R ψ, hochschildDifferential_smul, LinearMap.smul_apply, hδψ,
      obstruction_apply_of_mem_filtration s.taylor_eq hz, neg_one_smul, neg_sub]
  refine ⟨⟨s.alg.gauge (-ψ) hφ hφ₁, by rw [gauge_grading, s.grading_eq],
    s.isMinimal.isMinimal_gauge hφ hφ₁,
    fun z hz ↦ s.isMinimal.taylor_gauge_apply_eq_of_hochschildDifferential s.grading_eq hφ hφ₁
      (by omega) s.taylor_eq hφe hδ hz,
    s.hom.comp (s.alg.gaugeHom (-ψ) hφ hφ₁), ?_⟩, fun z hz ↦ ?_⟩
  · rw [AInfinityHom.linearPart_comp, linearPart_gaugeHom, s.linearPart_hom, LinearMap.id_comp]
  -- The gauge morphism is the identity on the words of length at most `k + 1`.
  rw [AInfinityHom.taylor_comp, LinearMap.comp_apply, barMap_gaugeHom,
    coalgHom_letter_add_apply_eq_self_of_mem_filtration hφe hz]

variable (ℋ ℬ) in
/-- The successive stages of the killing procedure, starting from a stage agreeing with `ℋ` on the
words of length at most two. -/
private noncomputable def killingStage (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    (hHH : ∀ n (hn : 3 ≤ n), ℋ.HochschildVanishesAt ⟨n, by omega⟩)
    (s₀ : KillingStage ℋ ℬ 2) : (k : ℕ) → KillingStage ℋ ℬ (k + 2)
  | 0 => s₀
  | k + 1 => Classical.choose (exists_killingStage_succ hℋ hm (hHH (k + 3) (by omega))
      (killingStage hℋ hm hHH s₀ k))

/-- **Kadeishvili's intrinsic formality criterion**, over any commutative ring.  Let `ℋ` be a
graded algebra, presented as a minimal `A∞` algebra without operations above arity two, and
suppose that `HH^{n, 2 - n}(H, H) = 0` for every `n ≥ 3`: every Hochschild cocycle of `ℋ` of
suspended degree one concentrated on the words of length `n` is the Hochschild differential of a
cochain of suspended degree zero concentrated on the words of length `n - 1`.  Then every minimal
`A∞` structure `ℬ` with the grading and the binary operation of `ℋ` is `A∞` isomorphic to `ℋ`. -/
theorem IsMinimal.exists_isIso_of_forall_hochschildVanishesAt (hℬ : ℬ.IsMinimal)
    (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) (hG : ℬ.grading = ℋ.grading)
    (h₂ : ℬ.m 2 = ℋ.m 2)
    (hHH : ∀ n (hn : 3 ≤ n), ℋ.HochschildVanishesAt ⟨n, by omega⟩) :
    ∃ f : AInfinityHom ℬ ℋ, f.IsIso := by
  -- The first stage is `ℬ` itself, which agrees with `ℋ` on the words of length at most two.
  have hm₂ : ∀ k, 0 < k → k ≤ 2 → ℬ.m k = ℋ.m k := fun k hk hk₂ ↦ by
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    · exact MultilinearMap.ext fun x ↦ by rw [hℬ.m_one, hℋ.m_one]
    · exact h₂
  let s := killingStage ℋ ℬ hℋ hm hHH
    ⟨ℬ, hG, hℬ, fun _ hz ↦ taylor_apply_eq_of_forall_m_eq hG hm₂ hz, AInfinityHom.id ℬ,
      AInfinityHom.linearPart_id ℬ⟩
  -- The comparison morphisms of the successive stages stabilise.
  have hs : ∀ k, ∀ z ∈ filtration R A k, (s (k + 1)).hom.taylor z = (s k).hom.taylor z :=
    fun k z hz ↦ Classical.choose_spec (exists_killingStage_succ hℋ hm (hHH (k + 3) (by omega))
      (s k)) z (filtration_monotone R A k.le_succ hz)
  let f := AInfinityHom.limit (fun k ↦ (s k).hom) (fun k ↦ (s k).grading_eq)
    (fun k z hz ↦ (s k).taylor_eq z (filtration_monotone R A (by omega) hz)) hs
  have hf : Function.Bijective f.linearPart := by
    rw [AInfinityHom.linearPart_limit, (s 1).linearPart_hom]
    exact Function.bijective_id
  exact ⟨f.inverse hf, f.isIso_inverse hf⟩

end CommRing

section Field

variable {K : Type uK} {A : Type uA} [Field K] [AddCommGroup A] [Module K A]
  {ℋ : AInfinityAlgebra K A}

/-- **Kadeishvili's intrinsic formality criterion.**  Over a field, a graded algebra `ℋ`, presented
as a minimal `A∞` algebra without operations above arity two, is intrinsically formal when
`HH^{n, 2 - n}(H, H) = 0` for every `n ≥ 3`: every Hochschild cocycle of `ℋ` of suspended degree
one concentrated on the words of length `n` is the Hochschild differential of a cochain of
suspended degree zero concentrated on the words of length `n - 1`. -/
theorem isIntrinsicallyFormal_of_forall_hochschildVanishesAt (hℋ : ℋ.IsMinimal)
    (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    (hHH : ∀ n (hn : 3 ≤ n), ℋ.HochschildVanishesAt ⟨n, by omega⟩) :
    ℋ.IsIntrinsicallyFormal :=
  (isIntrinsicallyFormal_iff_forall_exists_isIso hℋ hm).2 fun _ hG hℬ h₂ ↦
    hℬ.exists_isIso_of_forall_hochschildVanishesAt hℋ hm hG h₂ hHH

end Field

end AInfinityAlgebra

end TauCeti
