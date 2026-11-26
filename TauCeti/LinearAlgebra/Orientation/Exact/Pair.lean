/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Exact.Basic
import TauCeti.LinearAlgebra.Ray

/-!
# Two short exact sequences meeting along a line

Let `T` be a finite-dimensional vector space over a linearly ordered field, with two short exact
sequences

`0 → A → T → A' → 0` (maps `Fa`, `Na`) and `0 → B → T → B' → 0` (maps `Fb`, `Nb`),

and a linear form `l` on `T`. The **comparison maps**

`Φ = (l ∘ Fa, Nb ∘ Fa) : A → K × B'` and `Ψ = (-l ∘ Fb, Na ∘ Fb) : B → K × A'`

compare each subspace with the line `K` measured by `l` followed by the quotient of the other
sequence. When `Φ` and `Ψ` are isomorphisms, the subspaces `Fa A` and `Fb B` meet in a line on
which `l` does not vanish, and their sum is `T`.

This is the linear algebra of the signs of Morse trajectories for a function `f` and for `-f`. At a
point of a trajectory from `p` to `q`, `T` is the tangent space, `Fa A` and `Fb B` are the tangent
spaces of the unstable manifold of `p` and of the stable manifold of `q`, `A'` and `B'` are their
normal spaces, and `l = df`. The trajectory of `-f` from `q` to `p` through the same point is
compared through `-l = d(-f)` and the roles of the two sequences are exchanged.

**The sign rule.** Orient `A`, `A'`, `B`, `B'`. The orientations of the two sequences induce
orientations `[A][A']` and `[B][B']` of `T`, each with the subspace first
(`Orientation.ofExact`), and the comparison maps either carry the orientations of `A` and `B` to
the orientations `[K][B']` and `[K][A']` or reverse them. Writing `±1` for these comparisons,
with `a' = dim A'` and `b' = dim B'`,

`sign Ψ = -(-1) ^ (b' * a') * ([B][B'] vs [A][A']) * sign Φ`

(`Orientation.ite_map_eq_prod_of_exact`). In bases: take `e ∈ Fa A ∩ Fb B` with `l e = 1`,
vectors `aᵢ` of `Fa A` spanning a complement of `e` on which `l` vanishes, and vectors `bⱼ` of
`Fb B` likewise. Then `e, a, b` computes `[A][A']` and `-e, b, a` computes `[B][B']`, and moving
the block `b` past the block `a` costs `(-1) ^ (a' * b')`.

## Main results

* `Orientation.ite_map_eq_prod_of_exact`: the sign rule.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` is the dual
  complex, up to the orientation conventions).
-/

public section
noncomputable section

open Module Function

namespace Orientation

variable {K T A A' B B' : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup T] [Module K T]
  [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
  [AddCommGroup B] [Module K B] [AddCommGroup B'] [Module K B']
  {Fa : A →ₗ[K] T} {Na : T →ₗ[K] A'} {Fb : B →ₗ[K] T} {Nb : T →ₗ[K] B'} {l : T →ₗ[K] K}

variable (K A' B') in
/-- The isomorphism `((t, v), u) ↦ ((-t, u), v)` from `(K × A') × B'` to `(K × B') × A'`, which
reverses the line `K` and exchanges the two blocks behind it. -/
private def exchangeEquiv : ((K × A') × B') ≃ₗ[K] ((K × B') × A') :=
  (LinearEquiv.prodAssoc K K A' B').trans
    (((LinearEquiv.neg K).prodCongr (LinearEquiv.prodComm K A' B')).trans
      (LinearEquiv.prodAssoc K K B' A').symm)


omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem exchangeEquiv_apply (t : K) (v : A') (u : B') :
    exchangeEquiv K A' B' ((t, v), u) = ((-t, u), v) := by
  simp [exchangeEquiv]

/-- Reversing the line and exchanging the two blocks behind it, before any reassociation,
multiplies the product orientation `[K]([A'][B'])` by `-(-1) ^ (a' * b')`. -/
private theorem map_neg_prodCongr_prodComm_prod [FiniteDimensional K A'] [FiniteDimensional K B']
    {a' b' : ℕ} (oA' : Orientation K A' (Fin a')) (oB' : Orientation K B' (Fin b'))
    (hA' : finrank K A' = a') (hB' : finrank K B' = b') :
    map (Fin (1 + (a' + b'))) ((LinearEquiv.neg K).prodCongr (LinearEquiv.prodComm K A' B'))
        (prod (Basis.singleton (Fin 1) K).orientation (prod oA' oB' hA' hB') (finrank_self K)
          (by rw [finrank_prod, hA', hB'])) =
      (-1 : Kˣ) ^ (1 + a' * b') • reindex K _ (finCongr (by omega))
        (prod (Basis.singleton (Fin 1) K).orientation (prod oB' oA' hB' hA') (finrank_self K)
          (by rw [finrank_prod, hA', hB'])) := by
  have hneg : map (Fin 1) (LinearEquiv.neg K : K ≃ₗ[K] K) (Basis.singleton (Fin 1) K).orientation =
      (-1 : Kˣ) ^ 1 • (Basis.singleton (Fin 1) K).orientation := by
    rw [map_linearEquiv_neg _ (by simp), finrank_self]
  rw [map_prod, hneg, map_prodComm_prod, prod_units_smul_left, prod_units_smul_right,
    prod_reindex_finCongr_right (add_comm b' a'), smul_smul, ← pow_add]

/-- Exchanging the two blocks behind a line and reversing the line multiplies the product
orientation by `-(-1) ^ (a' * b')`: `exchangeEquiv` carries `[K][A'][B']` to `-(-1) ^ (a' * b')`
times `[K][B'][A']`. It reassociates (`Orientation.map_prodAssoc_prod`), reverses the line and
exchanges the blocks (`map_neg_prodCongr_prodComm_prod`), and reassociates back
(`Orientation.map_prodAssoc_symm_prod`). -/
private theorem map_exchangeEquiv_prod_prod [FiniteDimensional K A'] [FiniteDimensional K B']
    {a' b' : ℕ} (oA' : Orientation K A' (Fin a'))
    (oB' : Orientation K B' (Fin b')) (hA' : finrank K A' = a') (hB' : finrank K B' = b') :
    map (Fin (1 + a' + b')) (exchangeEquiv K A' B')
        (prod (prod (Basis.singleton (Fin 1) K).orientation oA' (finrank_self K) hA') oB'
          (by rw [finrank_prod, finrank_self, hA']) hB') =
      (-1 : Kˣ) ^ (1 + a' * b') •
        reindex K _ (finCongr (by omega))
          (prod (prod (Basis.singleton (Fin 1) K).orientation oB' (finrank_self K) hB') oA'
            (by rw [finrank_prod, finrank_self, hB']) hA') := by
  simp only [exchangeEquiv, map_trans, map_prodAssoc_prod, map_reindex,
    map_neg_prodCongr_prodComm_prod, map_units_smul, map_prodAssoc_symm_prod, reindex_units_smul,
    reindex_finCongr_reindex_finCongr]

variable (hFa : Injective Fa) (hFaNa : Exact Fa Na) (hNa : Surjective Na)
  (hFb : Injective Fb) (hFbNb : Exact Fb Nb) (hNb : Surjective Nb)
  {eΦ : A ≃ₗ[K] K × B'} (heΦ : ∀ x, eΦ x = (l (Fa x), Nb (Fa x)))
  {eΨ : B ≃ₗ[K] K × A'} (heΨ : ∀ y, eΨ y = (-l (Fb y), Na (Fb y)))

include hFaNa hFbNb heΦ heΨ in
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Along the line `Fa A ∩ Fb B`, the two comparison maps are opposite on their first
components: the vector of `Fb B` read as `(t, 0)` by `Ψ` is the vector of `Fa A` read as
`(-t, 0)` by `Φ`. -/
private theorem apply_symm_eq_apply_symm_neg (t : K) :
    Fb (eΨ.symm (t, 0)) = Fa (eΦ.symm (-t, 0)) := by
  have hw : (-l (Fb (eΨ.symm (t, 0))), Na (Fb (eΨ.symm (t, 0)))) = (t, 0) :=
    (heΨ _).symm.trans (eΨ.apply_symm_apply _)
  obtain ⟨v, hv⟩ := (hFaNa _).1 (congrArg Prod.snd hw)
  rw [← hv, ← eΦ.symm_apply_apply v, heΦ, hv, hFbNb.apply_apply_eq_zero]
  congr 3
  linear_combination -congrArg Prod.fst hw

include hFa hFaNa heΨ in
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The splitting `G : (K × B') × A' ≃ T` of the sequence `0 → A → T → A' → 0` through `Φ`
(`Function.Exact.splitSurjectiveEquiv`) with the section `v ↦ Fb (Ψ⁻¹ (0, v))` of `Na`: it sends
`(x, v)` to `Fa (Φ⁻¹ x) + Fb (Ψ⁻¹ (0, v))`. -/
private theorem exists_linearEquiv_prod :
    ∃ G : ((K × B') × A') ≃ₗ[K] T, (∀ x, G (eΦ x, 0) = Fa x) ∧ (∀ z, Na (G z) = z.2) ∧
      ∀ x v, G (x, v) = Fa (eΦ.symm x) + Fb (eΨ.symm (0, v)) := by
  let s : A' →ₗ[K] T := Fb ∘ₗ eΨ.symm.toLinearMap ∘ₗ LinearMap.inr K K A'
  have hs : Na ∘ₗ s = .id :=
    LinearMap.ext fun v ↦ by simpa [s, heΨ] using congrArg Prod.snd (eΨ.apply_symm_apply (0, v))
  let e := hFaNa.splitSurjectiveEquiv hFa ⟨s, hs⟩
  -- Mathlib states no lemma for the inverse of `splitSurjectiveEquiv`: by definition it sends a
  -- splitting `e` to the section `e.1.symm ∘ₗ inr`. The properties `e.2` do not determine this
  -- section (every section of `Na` gives a splitting), so `hsymm` unfolds the definition once.
  have hsymm : ((hFaNa.splitSurjectiveEquiv hFa).symm e).val = e.val.symm ∘ₗ LinearMap.inr K A A' :=
    rfl
  have hinr : e.val.symm ∘ₗ LinearMap.inr K A A' = s := by
    rw [← hsymm, Equiv.symm_apply_apply]
  have he (x v) : e.val.symm (x, v) = Fa x + s v := by
    simp [LinearMap.congr_fun e.property.1 x, ← LinearMap.congr_fun hinr v, ← map_add]
  refine ⟨(eΦ.symm.prodCongr (LinearEquiv.refl K A')).trans e.val.symm, fun x ↦ ?_,
    fun z ↦ ?_, fun x v ↦ ?_⟩
  · simp [he]
  · simp [LinearMap.congr_fun e.property.2]
  · simp [he, s]

variable [FiniteDimensional K A] [FiniteDimensional K A'] [FiniteDimensional K B]
  [FiniteDimensional K B']

include hFaNa hFb hFbNb hNb heΦ heΨ in
omit [FiniteDimensional K A] in
/-- In the splitting `G` of the first sequence given by `exists_linearEquiv_prod`, precomposed
with `exchangeEquiv`, the second sequence splits too: the orientation `[B][B']` is
the image of the product orientation of `Ψ oB` and `oB'`. -/
private theorem ofExact_eq_map_exchangeEquiv_prod {G : ((K × B') × A') ≃ₗ[K] T}
    (hG : ∀ x v, G (x, v) = Fa (eΦ.symm x) + Fb (eΨ.symm (0, v))) {b b' : ℕ}
    (oB : Orientation K B (Fin b)) (oB' : Orientation K B' (Fin b')) (hB : finrank K B = b)
    (hB' : finrank K B' = b') :
    ofExact hFb hFbNb hNb oB oB' hB hB' = map _ ((exchangeEquiv K A' B').trans G)
      (prod (map _ eΨ oB) oB' (by rw [← hB, eΨ.finrank_eq]) hB') := by
  have hRG (t v u) : ((exchangeEquiv K A' B').trans G) ((t, v), u) =
      Fb (eΨ.symm (t, v)) + Fa (eΦ.symm (0, u)) := by
    have hsplit : eΨ.symm (t, v) = eΨ.symm (t, 0) + eΨ.symm (0, v) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    have hsplit' : eΦ.symm (-t, u) = eΦ.symm (-t, 0) + eΦ.symm (0, u) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [LinearEquiv.trans_apply, exchangeEquiv_apply, hG, hsplit, hsplit', map_add, map_add,
      apply_symm_eq_apply_symm_neg hFaNa hFbNb heΦ heΨ]
    abel
  refine ofExact_eq_map_prod hFb hFbNb hNb eΨ _ (fun y ↦ ?_) (fun ⟨⟨t, v⟩, u⟩ ↦ ?_) oB oB' hB hB'
  · rw [← Prod.mk.eta (p := eΨ y), hRG, Prod.mk.eta, eΨ.symm_apply_apply, Prod.mk_zero_zero,
      map_zero, map_zero, add_zero]
  · rw [hRG, map_add, hFbNb.apply_apply_eq_zero, zero_add]
    simpa [heΦ] using congrArg Prod.snd (eΦ.apply_symm_apply (0, u))

include heΦ heΨ in
open scoped Classical in
/-- **The sign rule for a pair of short exact sequences meeting along a line.** Let
`0 → A → T → A' → 0` and `0 → B → T → B' → 0` be short exact sequences, `l` a linear form on `T`,
and `Φ = (l ∘ Fa, Nb ∘ Fa)`, `Ψ = (-l ∘ Fb, Na ∘ Fb)` the comparison maps, isomorphisms
`A ≃ K × B'` and `B ≃ K × A'`. For orientations of `A`, `A'`, `B`, `B'`, write `sign Φ` for `1` if
`Φ` carries the orientation of `A` to the product orientation `[K][B']` and `-1` otherwise, and
likewise for `Ψ`. Then

`sign Ψ = -(-1) ^ (b' * a') * ε * sign Φ`,

where `ε` is `1` if the orientations `[B][B']` and `[A][A']` of `T` induced by the two sequences
agree, and `-1` otherwise. -/
theorem ite_map_eq_prod_of_exact {a a' b b' : ℕ} (hab : 1 + b' = a) (hba : 1 + a' = b)
    (oA : Orientation K A (Fin a)) (oA' : Orientation K A' (Fin a'))
    (oB : Orientation K B (Fin b)) (oB' : Orientation K B' (Fin b'))
    (hA : finrank K A = a) (hA' : finrank K A' = a') (hB : finrank K B = b)
    (hB' : finrank K B' = b') :
    (if map (Fin b) eΨ oB = reindex K (K × A') (finCongr hba)
        (prod (Basis.singleton (Fin 1) K).orientation oA' (finrank_self K) hA') then (1 : ℤ)
      else -1) =
      -(-1) ^ (b' * a') *
        (if reindex K T (finCongr (by omega)) (ofExact hFb hFbNb hNb oB oB' hB hB') =
            ofExact hFa hFaNa hNa oA oA' hA hA' then 1 else -1) *
        (if map (Fin a) eΦ oA = reindex K (K × B') (finCongr hab)
            (prod (Basis.singleton (Fin 1) K).orientation oB' (finrank_self K) hB') then 1
          else -1) := by
  subst hab hba
  have hX := map_exchangeEquiv_prod_prod oA' oB' hA' hB'
  set std := (Basis.singleton (Fin 1) K).orientation
  obtain ⟨G, hGa, hGNa, hG⟩ := exists_linearEquiv_prod (eΦ := eΦ) hFa hFaNa heΨ
  -- Write the orientations carried by `Φ` and `Ψ` as signed product orientations.
  obtain ⟨i, hi⟩ := (map _ eΦ oA).exists_eq_neg_one_pow_smul (prod std oB' (finrank_self K) hB')
    (by simp [finrank_prod, hB'])
  obtain ⟨j, hj⟩ := (map _ eΨ oB).exists_eq_neg_one_pow_smul (prod std oA' (finrank_self K) hA')
    (by simp [finrank_prod, hA'])
  rw [ofExact_eq_map_prod hFa hFaNa hNa eΦ G hGa hGNa oA oA' hA hA',
    ofExact_eq_map_exchangeEquiv_prod hFaNa hFb hFbNb hNb heΦ heΨ hG oB oB' hB hB', hi, hj]
  simp only [finCongr_refl, reindex_refl, Equiv.refl_apply, prod_units_smul_left, map_trans,
    map_units_smul, hX, map_reindex, reindex_units_smul, reindex_finCongr_reindex_finCongr,
    smul_smul, ← pow_add, Ray.ite_neg_one_pow_smul_eq_self, Ray.ite_neg_one_pow_smul_eq]
  simp [pow_add, mul_comm b' a', mul_assoc, mul_left_comm, ← mul_pow]

end Orientation
