/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Exact
import TauCeti.LinearAlgebra.Ray

/-!
# Two short exact sequences meeting along a line

Let `T` be a finite-dimensional vector space over a linearly ordered field, with two short exact
sequences

`0 → A → T → A' → 0` (maps `Fa`, `Na`) and `0 → B → T → B' → 0` (maps `Fb`, `Nb`),

and a linear form `l` on `T`. The **comparison maps**

`Φ = (l ∘ Fa, Nb ∘ Fa) : A → K × B'` and `Ψ = (-l ∘ Fb, Na ∘ Fb) : B → K × A'`

compare each subspace with the line `K` measured by `l` followed by the quotient of the other
sequence. If `Φ` is injective, then so is `Ψ`
(`Orientation.injective_prod_neg_comp_of_injective_prod_comp`, over any commutative ring). When
`Φ` and `Ψ` are isomorphisms, the subspaces `Fa A` and `Fb B` meet in a line on which `l` does not
vanish, and their sum is `T`.

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

* `Orientation.injective_prod_neg_comp_of_injective_prod_comp`: if `Φ` is injective, so is `Ψ`.
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

section CommRing

variable {K T A A' B B' : Type*} [CommRing K]
  [AddCommGroup T] [Module K T]
  [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
  [AddCommGroup B] [Module K B] [AddCommGroup B'] [Module K B']
  {Fa : A →ₗ[K] T} {Na : T →ₗ[K] A'} {Fb : B →ₗ[K] T} {Nb : T →ₗ[K] B'} {l : T →ₗ[K] K}

/-- If the comparison map `(l ∘ Fa, Nb ∘ Fa)` of a pair of short exact sequences
`0 → A → T → A'` and `0 → B → T → B'` is injective, so is the opposite comparison map
`(-l ∘ Fb, Na ∘ Fb)`: a vector `Fb y` killed by `l` and by `Na` is `Fa x` for an `x` killed by
the first comparison map. -/
theorem injective_prod_neg_comp_of_injective_prod_comp (hFaNa : Exact Fa Na) (hFb : Injective Fb)
    (hFbNb : Exact Fb Nb) (hΦ : Injective ((l ∘ₗ Fa).prod (Nb ∘ₗ Fa))) :
    Injective (((-l) ∘ₗ Fb).prod (Na ∘ₗ Fb)) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  have hl : l (Fb y) = 0 := by simpa using congrArg Prod.fst hy
  have hN : Na (Fb y) = 0 := by simpa using congrArg Prod.snd hy
  obtain ⟨x, hx⟩ := (hFaNa (Fb y)).1 hN
  have hx0 : x = 0 := hΦ.eq_iff' (map_zero _) |>.1 (by
    simp [hx, hl, hFbNb.apply_apply_eq_zero])
  exact hFb (by rw [← hx, hx0, map_zero, map_zero])

end CommRing

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
    exchangeEquiv K A' B' ((t, v), u) = ((-t, u), v) :=
  (LinearEquiv.prodAssoc K K B' A').symm_apply_eq.2 rfl

/-- Exchanging the two blocks behind a line and reversing the line multiplies the product
orientation by `-(-1) ^ (a' * b')`: `exchangeEquiv` carries `[K][A'][B']` to `-(-1) ^ (a' * b')`
times `[K][B'][A']`. -/
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
  set std := (Basis.singleton (Fin 1) K).orientation
  have hassoc := map_prodAssoc_prod std oA' oB' (finrank_self K) hA' hB'
  have hassoc' := map_prodAssoc_prod std oB' oA' (finrank_self K) hB' hA'
  have hneg : map (Fin 1) (LinearEquiv.neg K : K ≃ₗ[K] K) std = (-1 : Kˣ) ^ 1 • std := by
    rw [map_linearEquiv_neg std (by simp), finrank_self]
  -- The reassociation back is the inverse of `hassoc'`.
  have hassoc'' : map (Fin (1 + (b' + a'))) (LinearEquiv.prodAssoc K K B' A').symm
      (prod std (prod oB' oA' hB' hA') (finrank_self K) (by rw [finrank_prod, hB', hA'])) =
      reindex K _ (finCongr (add_assoc 1 b' a'))
        (prod (prod std oB' (finrank_self K) hB') oA'
          (by rw [finrank_prod, finrank_self, hB']) hA') := by
    rw [← (map (Fin (1 + (b' + a'))) (LinearEquiv.prodAssoc K K B' A')).injective.eq_iff,
      ← map_symm, Equiv.apply_symm_apply, map_reindex, hassoc',
      reindex_finCongr_reindex_finCongr, finCongr_refl, reindex_refl, Equiv.refl_apply]
  rw [exchangeEquiv, map_trans, map_trans, hassoc, map_reindex, map_prod, hneg,
    map_prodComm_prod oA' oB' hA' hB', prod_units_smul_left, prod_units_smul_right,
    prod_reindex_finCongr_right (add_comm b' a'), reindex_units_smul, reindex_units_smul,
    reindex_finCongr_reindex_finCongr, map_units_smul, map_units_smul, map_reindex, hassoc'',
    reindex_finCongr_reindex_finCongr, smul_smul, ← pow_add]

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
/-- The isomorphism `(K × B') × A' ≃ T` sending `(x, v)` to `Fa (Φ⁻¹ x) + Fb (Ψ⁻¹ (0, v))`. It
splits the sequence `0 → A → T → A' → 0` through `Φ`, with the section `v ↦ Fb (Ψ⁻¹ (0, v))` of
`Na`. -/
private theorem exists_linearEquiv_prod :
    ∃ G : ((K × B') × A') ≃ₗ[K] T, ∀ x v, G (x, v) = Fa (eΦ.symm x) + Fb (eΨ.symm (0, v)) := by
  have hNa' (v : A') : Na (Fb (eΨ.symm (0, v))) = v :=
    congrArg Prod.snd ((heΨ _).symm.trans (eΨ.apply_symm_apply (0, v)))
  set G : ((K × B') × A') →ₗ[K] T :=
    (Fa ∘ₗ eΦ.symm.toLinearMap).coprod (Fb ∘ₗ eΨ.symm.toLinearMap ∘ₗ LinearMap.inr K K A')
  have hG (x v) : G (x, v) = Fa (eΦ.symm x) + Fb (eΨ.symm (0, v)) := rfl
  have hNaG (x v) : Na (G (x, v)) = v := by
    rw [hG, map_add, hFaNa.apply_apply_eq_zero, hNa', zero_add]
  refine ⟨LinearEquiv.ofBijective G ⟨(injective_iff_map_eq_zero G).2 fun z hz ↦ ?_, fun t ↦ ?_⟩,
    hG⟩
  · obtain ⟨x, v⟩ := z
    obtain rfl : v = 0 := by rw [← hNaG x v, hz, map_zero]
    rw [hG, Prod.mk_zero_zero, map_zero, map_zero, add_zero, map_eq_zero_iff _ hFa,
      LinearEquiv.map_eq_zero_iff] at hz
    rw [hz, Prod.mk_zero_zero]
  · obtain ⟨x, hx⟩ := (hFaNa (t - Fb (eΨ.symm (0, Na t)))).1 (by rw [map_sub, hNa', sub_self])
    exact ⟨(eΦ x, Na t), by rw [hG, eΦ.symm_apply_apply, hx, sub_add_cancel]⟩

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
    exact congrArg Prod.snd ((heΦ _).symm.trans (eΦ.apply_symm_apply (0, u)))


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
  obtain ⟨G, hG⟩ := exists_linearEquiv_prod (eΦ := eΦ) hFa hFaNa heΨ
  -- Both induced orientations of `T` are transported product orientations.
  have hA_eq := ofExact_eq_map_prod hFa hFaNa hNa eΦ G
    (fun x ↦ by rw [hG, eΦ.symm_apply_apply, Prod.mk_zero_zero, map_zero, map_zero, add_zero])
    (fun ⟨x, v⟩ ↦ by
      rw [hG, map_add, hFaNa.apply_apply_eq_zero, zero_add]
      exact congrArg Prod.snd ((heΨ _).symm.trans (eΨ.apply_symm_apply (0, v)))) oA oA' hA hA'
  have hB_eq := ofExact_eq_map_exchangeEquiv_prod hFaNa hFb hFbNb hNb heΦ heΨ hG oB oB' hB hB'
  rw [hA_eq, hB_eq]
  rcases (map _ eΦ oA).eq_or_eq_neg (prod std oB' (finrank_self K) hB')
      (by simp [finrank_prod, hB']) with hs | hs <;>
    rcases (map _ eΨ oB).eq_or_eq_neg (prod std oA' (finrank_self K) hA')
      (by simp [finrank_prod, hA']) with hs' | hs' <;>
    simp only [hs, hs', prod_neg_left, Orientation.map_neg, Orientation.reindex_neg, map_trans,
      hX, map_units_smul, map_reindex, reindex_units_smul, reindex_finCongr_reindex_finCongr,
      finCongr_refl, reindex_refl, Equiv.refl_apply] <;>
    rcases Nat.even_or_odd (a' * b') with he | he <;>
    simp [pow_add, he.neg_one_pow, mul_comm b' a', Module.Ray.neg_units_smul,
      Module.Ray.ne_neg_self, Module.Ray.neg_neg,
      (Module.Ray.ne_neg_self (std.prod oA' (finrank_self K) hA')).symm,
      (Module.Ray.ne_neg_self (std.prod oB' (finrank_self K) hB')).symm,
      (Module.Ray.ne_neg_self (map (Fin (1 + b' + a')) G
        ((std.prod oB' (finrank_self K) hB').prod oA'
          (by rw [finrank_prod, finrank_self, hB']) hA'))).symm]

end Orientation
