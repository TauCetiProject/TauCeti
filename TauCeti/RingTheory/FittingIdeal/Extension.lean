/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Presentation.Quadratic

import TauCeti.Algebra.Module.Projective.Schanuel

/-!
# Fitting ideals of extensions

Let `R` be a commutative ring and `0 → A → B → C → 0` a short exact sequence of finite
`R`-modules. The zeroth Fitting ideal is not multiplicative in general: for `R = k[x, y]` with
maximal ideal `𝔪 = (x, y)`, the sequence `0 → 𝔪/𝔪² → R/𝔪² → R/𝔪 → 0` has `Fitt₀ = 𝔪²` in the
middle and `𝔪² · 𝔪 = 𝔪³` on the outside. When `C` is quadratically presented, it is
multiplicative:

  `Fitt₀(B) = Fitt₀(A) Fitt₀(C)`.

More generally, if `C` is the cokernel of an endomorphism `φ` of a finite free module `G`, then
`Fitt₀(B) = Fitt₀(A) (det φ)`, with no hypothesis on `A` beyond finiteness. Indeed, for a
surjection `F → A` from a finite free module and a lift `G → B` of the generators of `C`, the
relations of `B` are the image of `ker (F → A) × G` under an endomorphism
`(x, z) ↦ (x - X z, φ z)` of `F × G` (`TauCeti.ker_coprod_eq_map_prod_top`), of determinant
`det φ`, so their maximal minors are those of `ker (F → A) × G` scaled by `det φ`.

Comparing the two extensions of `B` and `B'` by `A'` and `A` that make up the fibre product
`B ×_C B'` gives the second identity of Dasgupta and Kakde: for two extensions
`0 → A → B → C → 0` and `0 → A' → B' → C → 0` of a common quotient by finite modules, with `B`
and `B'` quadratically presented, `Fitt₀(A) Fitt₀(B') = Fitt₀(A') Fitt₀(B)`.

## Main results

* `TauCeti.fittingIdeal_zero_eq_mul_span_det_of_exact`: `Fitt₀(B) = Fitt₀(A) (det φ)` when `C` is
  the cokernel of `φ`.
* `TauCeti.fittingIdeal_eq_mul_of_exact`: `Fitt₀(B) = Fitt₀(A) Fitt₀(C)` when `C` is
  quadratically presented.
* `TauCeti.fittingIdeal_mul_comm_of_exact`: `Fitt₀(A) Fitt₀(B') = Fitt₀(A') Fitt₀(B)` for two
  extensions of a common quotient with quadratically presented middle terms.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  Lemmas 2.6 and 2.7.
-/

public section

open Module LinearMap

namespace TauCeti

variable {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup C] [Module R C] {i : A →ₗ[R] B} {q : B →ₗ[R] C}

/-- **The Fitting ideal of an extension of the cokernel of an endomorphism.** Let
`0 → A → B → C → 0` be a short exact sequence of finite modules, and let `C` be presented as the
cokernel of an endomorphism `φ` of a finite free module. Then `Fitt₀(B) = Fitt₀(A) (det φ)`. -/
theorem fittingIdeal_zero_eq_mul_span_det_of_exact [Module.Finite R A] [Module.Finite R B]
    {G : Type*} [AddCommGroup G] [Module R G] [Module.Free R G] [Module.Finite R G]
    (hi : Function.Injective i) (hq : Function.Surjective q) (hiq : Function.Exact i q)
    (φ : G →ₗ[R] G) {π : G →ₗ[R] C} (hπ : Function.Surjective π) (hφ : ker π = range φ) :
    fittingIdeal R B 0 = fittingIdeal R A 0 * Ideal.span {φ.det} := by
  nontriviality R
  obtain ⟨n, πA, hπA⟩ := Module.Finite.exists_fin' R A
  -- Lift the generators of `C` to `c : G → B`, and the lifted relations to `X : G → R^n`.
  obtain ⟨c, hc⟩ := Module.projective_lifting_property q π hq
  obtain ⟨X, hX⟩ := exists_comp_eq_of_range_le (a := c ∘ₗ φ) (b := i ∘ₗ πA) <| by
    rw [range_comp_of_range_eq_top i (range_eq_top.2 hπA), ← hiq.linearMap_ker_eq, range_le_ker_iff,
      ← comp_assoc, hc, ← range_le_ker_iff, hφ]
  -- The relations of `B` are the image of `ker πA × G` under `T : (x, z) ↦ (x - X z, φ z)`.
  set T := (fst R (Fin n → R) G - X ∘ₗ snd R (Fin n → R) G).prod (φ ∘ₗ snd R (Fin n → R) G)
  have hT : T = (LinearMap.id.prodMap φ) ∘ₗ (1 + (-(inl R (Fin n → R) G ∘ₗ X)) ∘ₗ snd R _ G) := by
    ext <;> simp [T, sub_eq_add_neg]
  have hdet : T.det = φ.det := by
    have h0 : snd R (Fin n → R) G ∘ₗ (-(inl R (Fin n → R) G ∘ₗ X)) = 0 := by
      ext
      simp
    rw [hT, det_comp, det_prodMap, det_id, one_mul, det_one_add_comp_comm, h0, add_zero, map_one,
      mul_one]
  rw [fittingIdeal_eq_minorsIdeal_ker (hiq.surjective_coprod hπA hπ hc), Nat.sub_zero,
    ker_coprod_eq_map_prod_top hi hiq.linearMap_comp_eq_zero πA hφ.symm hc hX,
    minorsIdeal_map_finrank, hdet, finrank_prod, Submodule.minorsIdeal_prod_top,
    fittingIdeal_eq_minorsIdeal_ker hπA, Nat.sub_zero, mul_comm]

/-- **The Fitting ideal of an extension with a quadratically presented quotient**
(Dasgupta–Kakde, Lemma 2.6). For a short exact sequence `0 → A → B → C → 0` of finite modules
with `C` quadratically presented, `Fitt₀(B) = Fitt₀(A) Fitt₀(C)`. -/
theorem fittingIdeal_eq_mul_of_exact [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    (hi : Function.Injective i) (hq : Function.Surjective q) (hiq : Function.Exact i q)
    (hC : IsQuadraticallyPresented R C) :
    fittingIdeal R B 0 = fittingIdeal R A 0 * fittingIdeal R C 0 := by
  obtain ⟨m, hm, M, ⟨e⟩⟩ := isQuadraticallyPresented_iff_exists_linearEquiv.1 hC
  let P := (QuadraticPresentation.cokernel hm M).map e
  rw [P.fittingIdeal_eq, fittingIdeal_zero_eq_mul_span_det_of_exact hi hq hiq (Matrix.toLin' P.rel)
    P.gen_surjective P.range_rel_eq_ker.symm, LinearMap.det_toLin']

/-- **Fitting ideals of two extensions of a common quotient** (Dasgupta–Kakde, Lemma 2.7). For
short exact sequences `0 → A → B → C → 0` and `0 → A' → B' → C → 0` of finite modules with `B`
and `B'` quadratically presented, `Fitt₀(A) Fitt₀(B') = Fitt₀(A') Fitt₀(B)`. Both sides are the
zeroth Fitting ideal of the fibre product `B ×_C B'`. -/
theorem fittingIdeal_mul_comm_of_exact {A' B' : Type*} [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B'] [Module.Finite R A] [Module.Finite R B] [Module.Finite R A']
    [Module.Finite R B'] {i' : A' →ₗ[R] B'} {q' : B' →ₗ[R] C} (hi : Function.Injective i)
    (hq : Function.Surjective q) (hiq : Function.Exact i q) (hi' : Function.Injective i')
    (hq' : Function.Surjective q') (hiq' : Function.Exact i' q')
    (hB : IsQuadraticallyPresented R B) (hB' : IsQuadraticallyPresented R B') :
    fittingIdeal R A 0 * fittingIdeal R B' 0 = fittingIdeal R A' 0 * fittingIdeal R B 0 := by
  -- The fibre product `P = B ×_C B'` is an extension of `B` by `A'` and of `B'` by `A`.
  let P := ker (q ∘ₗ fst R B B' - q' ∘ₗ snd R B B')
  have hmem {b : B} {b' : B'} : (b, b') ∈ P ↔ q b = q' b' := by
    simp [P, sub_eq_zero]
  let j : A →ₗ[R] P := (inl R B B' ∘ₗ i).codRestrict P fun a ↦ hmem.2 <| by
    simp [hiq.apply_apply_eq_zero]
  let j' : A' →ₗ[R] P := (inr R B B' ∘ₗ i').codRestrict P fun a ↦ hmem.2 <| by
    simp [hiq'.apply_apply_eq_zero]
  let p : P →ₗ[R] B := fst R B B' ∘ₗ P.subtype
  let p' : P →ₗ[R] B' := snd R B B' ∘ₗ P.subtype
  have hj : Function.Injective j := fun a b h ↦ hi congr(Prod.fst (Subtype.val $h))
  have hj' : Function.Injective j' := fun a b h ↦ hi' congr(Prod.snd (Subtype.val $h))
  have hp : Function.Surjective p := fun b ↦ by
    obtain ⟨b', hb'⟩ := hq' (q b)
    exact ⟨⟨(b, b'), hmem.2 hb'.symm⟩, rfl⟩
  have hp' : Function.Surjective p' := fun b' ↦ by
    obtain ⟨b, hb⟩ := hq (q' b')
    exact ⟨⟨(b, b'), hmem.2 hb⟩, rfl⟩
  have hjp' : Function.Exact j p' := by
    rintro ⟨⟨b, b'⟩, hx⟩
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain rfl : b' = 0 := h
      obtain ⟨a, rfl⟩ := (hiq b).1 (by simpa using hmem.1 hx)
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      exact congr(Prod.snd (Subtype.val $ha)).symm
  have hj'p : Function.Exact j' p := by
    rintro ⟨⟨b, b'⟩, hx⟩
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain rfl : b = 0 := h
      obtain ⟨a', rfl⟩ := (hiq' b').1 (by simpa using (hmem.1 hx).symm)
      exact ⟨a', rfl⟩
    · rintro ⟨a', ha'⟩
      exact congr(Prod.fst (Subtype.val $ha')).symm
  have : Module.Finite R P := Module.Finite.of_exact hj'p hp
  rw [← fittingIdeal_eq_mul_of_exact hj hp' hjp' hB',
    ← fittingIdeal_eq_mul_of_exact hj' hp hj'p hB]

end TauCeti
