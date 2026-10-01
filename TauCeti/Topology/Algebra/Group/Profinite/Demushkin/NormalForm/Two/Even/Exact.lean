/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.NeTwo
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Approximation
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Automorphism

/-!
# Labute's normal form for the dyadic Demushkin groups of even rank

Let `F = freeProP 2 (Fin n)` be the free pro-`2` group on an even number `n` of generators and let
`r ∈ Φ(F)` be a relator presenting a Demushkin group `G = ⟨x₁, …, x_n ∣ r⟩` with `q(G) = 2`.
Labute's Theorem 3 says that a continuous automorphism of `F` carries `r` to one of the words

  `x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, `2 ≤ f < ∞`, or
  `x₁^{2+α} (x₁, x₂) (x₃, x₄) ⋯ (x_{n-1}, x_n)`, the value `f = ∞`,

with a `2`-adic exponent `α ∈ 4ℤ₂`, so that `G` is presented by that word. This file proves it, by
Labute's route (pp. 118–119). Since `q(G) = 2`, the cup form of `G` is not alternating, and the
normal form modulo `λ_2(F)` carries the class of `r` to that of `x₁² (x₁, x₂) ⋯ (x_{n-1}, x_n)`
(`TauCeti.IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven`); the
successive approximation with tails then carries `r` itself to the intermediate form
`x₁^{2+α} (x₁, x₂) · ((x₃, x₄) ⋯ (x_{n-1}, x_n) x₃^{α₃} ⋯ x_n^{α_n})` with `2`-adic exponents
divisible by `4`
(`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul`). At rank
`n = 2` there is no tail relator and the theorem is proved. For `n ≥ 4`, the tail relator
`r' = (x₃, x₄) ⋯ (x_{n-1}, x_n) x₃^{α₃} ⋯ x_n^{α_n}` is a word in `x₃, …, x_n` alone. Read in the
free pro-`2` group on those `n - 2 ≥ 2` generators, `r'` has the class of
`(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1`, so it presents a Demushkin group whose `q`-invariant is not
`2`, and the normal-form theorem for `q ≠ 2`
(`TauCeti.freeProP.exists_continuousMulEquiv_apply_demushkinWordNeTwo_zero_mul_eq`) carries `r'`
to `x₃^{q'} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with `q' = 0` or `q' = 2^f`, `f ≥ 2`. Extending that
automorphism to `F` by fixing `x₁` and `x₂` (`TauCeti.freeProP.finSuccExtend`, twice) gives the
theorem.

The exponent `α` is a genuine `2`-adic integer, so the normal form is written with the `2`-adic
power `x₁ ^ (2 + α)` of `TauCeti.IsProP.padicPow` rather than as the word
`TauCeti.demushkinWordTwoEven`, whose exponent is a natural number. The parameters `α` and `f` are
not identified here: by the corollary to Labute's Theorem 4, the image of the canonical character
of `G` is `{±1} × U^(f)` when `2^f ∣ α` and the twisted subgroup `U^[v₂(α)]` otherwise, which is
how the classification pins them, and this file proves only the existence of the normal form.

## Main results

* `exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo`, in the
  namespace `TauCeti.freeProP`: a relator of `F` with the class of `x₁² (x₁, x₂) ⋯ (x_{n-1}, x_n)`
  in `gr_1(F)`, `n` even, is carried by a continuous automorphism of `F` to
  `x₁^{2+α} (x₁, x₂) x₃^{q'} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with `4 ∣ α` in `ℤ₂` and `q' = 0` or
  `q' = 2^f` for some `f ≥ 2`.
* `exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo`, in the
  namespace `TauCeti.IsDemushkin`: **Labute's Theorem 3 for `q = 2` and even rank**, the previous
  statement for a relator in `Φ(F)` presenting a Demushkin group with `q = 2` on an even number of
  generators.
* `exists_continuousMulEquiv_presentedProP_padicPow_mul_labuteComm_mul_demushkinWordNeTwo`, in the
  namespace `TauCeti.IsDemushkin`: a Demushkin group at `p = 2` of even rank `n` with `q = 2` is
  topologically isomorphic to
  `⟨x₁, …, x_n ∣ x₁^{2+α} (x₁, x₂) x₃^{q'} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` for such `α` and `q'`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorem 3, case (3).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

universe u

namespace freeProP

variable {k : ℕ}

/-- `freeProP.map Fin.succ` carries a `2`-adic power of a generator of the free pro-`2` group on
`k` generators to the same `2`-adic power of the shifted generator. -/
private theorem map_succ_padicPow (j : Fin k) (c : ℤ_[2]) :
    map (Fin.succ : Fin k → Fin (k + 1)) ((isProP_freeProP 2 (Fin k)).padicPow (of j) c) =
      (isProP_freeProP 2 (Fin (k + 1))).padicPow (of j.succ) c := by
  have h := (isProP_freeProP 2 (Fin k)).map_padicPow (isProP_freeProP 2 (Fin (k + 1)))
    (map (p := 2) (Fin.succ : Fin k → Fin (k + 1)) : freeProP 2 (Fin k) →* freeProP 2 (Fin (k + 1)))
    (by exact (map Fin.succ).continuous) (of j) c
  rwa [MonoidHom.coe_ofClass, map_of] at h

/-- The generators `x₃, …, x_{k+2}` of the free pro-`2` group on `k + 2` generators are the images
of the generators `x₁, …, x_k` of the free pro-`2` group on `k` generators under
`freeProP.map Fin.succ`, applied twice. -/
private theorem map_succ_map_succ_freeProPGen (i : ℕ) :
    map (Fin.succ : Fin (k + 1) → Fin (k + 2)) (map (Fin.succ : Fin k → Fin (k + 1))
      (freeProPGen 2 k i)) = freeProPGen 2 (k + 2) (i + 2) := by
  rw [map_succ_freeProPGen, map_succ_freeProPGen]

/-- **The tail relator, read on `x₁, …, x_{n-2}`.** For a family of `2`-adic exponents `a` on the
generators of the free pro-`2` group on `k + 2` generators, the tail relator
`(x₃, x₄) ⋯ (x_{k+1}, x_{k+2}) x₃^{a₃} ⋯ x_{k+2}^{a_{k+2}}` is the image under
`freeProP.map Fin.succ`, applied twice, of the relator
`(x₁, x₂) ⋯ (x_{k-1}, x_k) x₁^{a₃} ⋯ x_k^{a_{k+2}}` of the free pro-`2` group on `k` generators. -/
private theorem demushkinWordNeTwo_mul_prod_tail_eq (a : Fin (k + 2) → ℤ_[2]) :
    demushkinWordNeTwo 0 k (fun i ↦ freeProPGen 2 (k + 2) (i + 2)) *
        (((List.finRange (k + 2)).drop 2).map fun i ↦
          (isProP_freeProP 2 (Fin (k + 2))).padicPow (of i) (a i)).prod =
      map (Fin.succ : Fin (k + 1) → Fin (k + 2)) (map (Fin.succ : Fin k → Fin (k + 1))
        (demushkinWordNeTwo 0 k (freeProPGen 2 k) *
          ((List.finRange k).map fun j ↦
            (isProP_freeProP 2 (Fin k)).padicPow (of j) (a j.succ.succ)).prod)) := by
  simp only [map_mul, map_demushkinWordNeTwo, map_list_prod, List.map_map, Function.comp_def,
    map_succ_map_succ_freeProPGen, map_succ_padicPow, List.finRange_succ, List.map_cons,
    List.drop_succ_cons, List.drop_zero]

/-- **The exact form of the dyadic relators of even rank.** Let `n ≥ 2` be even and let
`r ∈ λ_1(F)` be a relator of the free pro-`2` group `F` on `n` generators with the class of
`x₁² (x₁, x₂) (x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1(F)`. Then a continuous automorphism of `F` carries
`r` to `x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, where `α ∈ ℤ₂` is divisible by `4` and
`q = 0`, Labute's level `f = ∞`, or `q = 2^f` for some `f ≥ 2`. The last factor is the `q ≠ 2` word
`x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)` on `n - 2` letters, read on the generators shifted by two. The
theorem assumes only the degree-one class of `r`, not that `r` is the relator of a Demushkin
group. -/
theorem exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo {n : ℕ}
    (hn : Even n) (hn0 : 0 < n) (r : pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (h : gradedMk 2 (freeProP 2 (Fin n)) 1 r = gradedMk 2 (freeProP 2 (Fin n)) 1
      ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _⟩) :
    ∃ (e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n)) (α : ℤ_[2]) (q : ℕ),
      (4 : ℤ_[2]) ∣ α ∧ (q = 0 ∨ ∃ f, 2 ≤ f ∧ q = 2 ^ f) ∧
        e r = (isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
          labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
          demushkinWordNeTwo q (n - 2) fun i ↦ freeProPGen 2 n (i + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    omega
  -- The intermediate form: `e₁ r = x₁^{2+α} (x₁, x₂) · ((x₃, x₄) ⋯ (x_{n-1}, x_n) t₃ ⋯ t_n)`, with
  -- each tail `t_i = x_i^{a_i}` a `2`-adic power of `x_i` whose exponent is divisible by `4`.
  obtain ⟨e₁, α, a, hα, ha, he₁⟩ :=
    exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul hn hn0 r h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : Even k := by
    obtain ⟨m, hm⟩ := hn
    exact ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at he₁ ⊢
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · -- Rank two: there is no tail relator, and the relator is already `x₁^{2+α} (x₁, x₂)`.
    refine ⟨e₁, α, 0, hα, Or.inl rfl, ?_⟩
    rw [he₁]
    simp [demushkinWordNeTwo_def, List.finRange_succ]
  -- The tail relator, read on `x₃, …, x_n`, is normalised by the case `q ≠ 2`.
  set T : freeProP 2 (Fin k) := ((List.finRange k).map fun j ↦
    (isProP_freeProP 2 (Fin k)).padicPow (of j) (a j.succ.succ)).prod with hT_def
  have h4 : ((2 : ℕ) : ℤ_[2]) ^ 2 = 4 := by norm_num
  have hT : T ∈ pLowerCentralSeries 2 (freeProP 2 (Fin k)) 2 :=
    (pLowerCentralSeries 2 (freeProP 2 (Fin k)) 2).list_prod_mem fun x hx ↦ by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact (padicPow_mem_pLowerCentralSeries_iff j _ 2).2 (h4 ▸ ha _)
  obtain ⟨e', q, hq', he'⟩ :=
    exists_continuousMulEquiv_apply_demushkinWordNeTwo_zero_mul_eq hk hkpos.ne' hT
  -- The extension `E` of its normalising automorphism by `x₁ ↦ x₁` and `x₂ ↦ x₂` fixes the head
  -- `x₁^{2+α} (x₁, x₂)` and carries the embedded tail relator to
  -- `x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)`.
  set E : freeProP 2 (Fin (k + 2)) ≃ₜ* freeProP 2 (Fin (k + 2)) :=
    finSuccExtend (finSuccExtend e') with hE_def
  have hE0 : E (freeProPGen 2 (k + 2) 0) = freeProPGen 2 (k + 2) 0 :=
    finSuccExtend_freeProPGen_zero _
  have hE1 : E (freeProPGen 2 (k + 2) 1) = freeProPGen 2 (k + 2) 1 := by
    have h1 : freeProPGen 2 (k + 2) 1 = map Fin.succ (freeProPGen 2 (k + 1) 0) :=
      (map_succ_freeProPGen 0).symm
    rw [h1, hE_def, finSuccExtend_map_succ, finSuccExtend_freeProPGen_zero]
  have hEhead : E ((isProP_freeProP 2 (Fin (k + 2))).padicPow (freeProPGen 2 (k + 2) 0) (2 + α) *
        labuteComm (freeProPGen 2 (k + 2) 0) (freeProPGen 2 (k + 2) 1)) =
      (isProP_freeProP 2 (Fin (k + 2))).padicPow (freeProPGen 2 (k + 2) 0) (2 + α) *
        labuteComm (freeProPGen 2 (k + 2) 0) (freeProPGen 2 (k + 2) 1) := by
    have hmap := (isProP_freeProP 2 (Fin (k + 2))).map_padicPow (isProP_freeProP 2 (Fin (k + 2)))
      (E : freeProP 2 (Fin (k + 2)) →* freeProP 2 (Fin (k + 2))) E.continuous
      (freeProPGen 2 (k + 2) 0) (2 + α)
    rw [MonoidHom.coe_ofClass] at hmap
    simp only [map_mul, map_labuteComm, hmap, hE0, hE1]
  have hEtail : E (map (Fin.succ : Fin (k + 1) → Fin (k + 2))
        (map (Fin.succ : Fin k → Fin (k + 1)) (demushkinWordNeTwo 0 k (freeProPGen 2 k) * T))) =
      demushkinWordNeTwo q k fun i ↦ freeProPGen 2 (k + 2) (i + 2) := by
    rw [hE_def, finSuccExtend_map_succ, finSuccExtend_map_succ, he']
    simp only [map_demushkinWordNeTwo, Function.comp_def, map_succ_map_succ_freeProPGen]
  have he : E (e₁ r) =
      (isProP_freeProP 2 (Fin (k + 2))).padicPow (freeProPGen 2 (k + 2) 0) (2 + α) *
        labuteComm (freeProPGen 2 (k + 2) 0) (freeProPGen 2 (k + 2) 1) *
        demushkinWordNeTwo q k fun i ↦ freeProPGen 2 (k + 2) (i + 2) := by
    rw [he₁, demushkinWordNeTwo_mul_prod_tail_eq a, map_mul, hEhead, hEtail]
  refine ⟨e₁.trans E, α, q, hα, hq', ?_⟩
  rw [ContinuousMulEquiv.trans_apply, he]

end freeProP

namespace IsDemushkin

/-- **Labute's normal form for `q = 2` and even rank** (Labute, Theorem 3, case (3)). Let
`r ∈ Φ(F)` be a relator of the free pro-`2` group on an even number `n` of generators presenting a
Demushkin group `G = ⟨x₁, …, x_n ∣ r⟩` with `q(G) = 2`. Then a continuous automorphism of `F`
carries `r` to `x₁^{2+α} (x₁, x₂) x₃^{q'} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, where `α ∈ ℤ₂` is divisible
by `4` and `q' = 0`, Labute's level `f = ∞`, or `q' = 2^f` for some `f ≥ 2`. The last factor is the
`q ≠ 2` word `x₃^{q'} (x₃, x₄) ⋯ (x_{n-1}, x_n)` on `n - 2` letters, read on the generators shifted
by two. -/
theorem exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo {n : ℕ}
    (hn : Even n) {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) (hq : demushkinQ hG = 2) :
    ∃ (e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n)) (α : ℤ_[2]) (q : ℕ),
      (4 : ℤ_[2]) ∣ α ∧ (q = 0 ∨ ∃ f, 2 ≤ f ∧ q = 2 ^ f) ∧
        e r = (isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
          labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
          demushkinWordNeTwo q (n - 2) fun i ↦ freeProPGen 2 n (i + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- A Demushkin group has positive rank, so `n ≥ 2`.
  have hn0 : 0 < n := by
    have := hG.demushkinRank_pos
    rwa [demushkinRank_presentedProP (Set.singleton_subset_iff.2 hr) hG, Nat.card_fin] at this
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hr₁ : r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le hr
  -- Since `q(G) = 2`, the degree-one form of `r` is not alternating, and the normal form modulo
  -- `λ_2(F)` carries the class of `r` to that of `x₁² (x₁, x₂) (x₃, x₄) ⋯ (x_{n-1}, x_n)`.
  obtain ⟨e₀, he₀⟩ := hG.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven hr
    (ContinuousMulEquiv.refl _) (hG.exists_cupFp_self_ne_zero_iff_demushkinQ_eq_two.2 hq) hn
    (dvd_zero 4) le_rfl
  have hmem : e₀ r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    (e₀ : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom.map_pLowerCentralSeries_le
      (e₀ : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ⟨r, hr₁, rfl⟩
  have h₀ : gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨e₀ r, hmem⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven 0 2 n (freeProPGen 2 n),
        demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_zero 2) two_pos n _⟩ := by
    rw [← he₀, gradedMap_gradedMk]
    rfl
  have h : gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨e₀ r, hmem⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _⟩ :=
    h₀.trans
      (gradedMk_demushkinWordTwoEven_eq_gradedMk_demushkinWordNeTwo (dvd_zero 2) le_rfl hn2 _)
  -- The exact form of a relator with that class.
  obtain ⟨e, α, q, hα, hq', he⟩ :=
    freeProP.exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo hn
      hn0 ⟨e₀ r, hmem⟩ h
  exact ⟨e₀.trans e, α, q, hα, hq', by rw [ContinuousMulEquiv.trans_apply]; exact he⟩

/-- **Labute's normal form for a Demushkin group of even rank with `q = 2`, intrinsic form**
(Labute, Theorem 3, case (3)). A Demushkin group `G` at `p = 2` of even rank `n = demushkinRank hG`
with `q(G) = 2` is topologically isomorphic to
`⟨x₁, …, x_n ∣ x₁^{2+α} (x₁, x₂) x₃^{q'} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` for some `α ∈ 4ℤ₂` and some
`q'` which is `0` or `2^f` with `f ≥ 2`. -/
theorem exists_continuousMulEquiv_presentedProP_padicPow_mul_labuteComm_mul_demushkinWordNeTwo
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (hG : IsDemushkin 2 G) (hn : Even (demushkinRank hG))
    (hq : demushkinQ hG = 2) :
    ∃ (α : ℤ_[2]) (q : ℕ), (4 : ℤ_[2]) ∣ α ∧ (q = 0 ∨ ∃ f, 2 ≤ f ∧ q = 2 ^ f) ∧
      Nonempty (G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
        {(isProP_freeProP 2 (Fin (demushkinRank hG))).padicPow
            (freeProPGen 2 (demushkinRank hG) 0) (2 + α) *
          labuteComm (freeProPGen 2 (demushkinRank hG) 0) (freeProPGen 2 (demushkinRank hG) 1) *
          demushkinWordNeTwo q (demushkinRank hG - 2) fun i ↦
            freeProPGen 2 (demushkinRank hG) (i + 2)}) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  have : Nonempty (Fin (demushkinRank hG)) := ⟨⟨0, hG.demushkinRank_pos⟩⟩
  have hG' : IsDemushkin 2 (presentedProP 2 (Fin (demushkinRank hG)) {r}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _)
      (hG.nondegenerate_degreeOneForm hr e)
  have hq' : demushkinQ hG' = 2 := (demushkinQ_congr hG' hG e).trans hq
  obtain ⟨e', α, q, hα, hq'', he'⟩ :=
    exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo hn hr hG' hq'
  exact ⟨α, q, hα, hq'', ⟨e.symm.trans (presentedProP.congrSingleton e' he')⟩⟩

end IsDemushkin

end TauCeti
