/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Criterion
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm

/-!
# Labute's normal forms modulo `λ_2` for the relator of a Demushkin group

Let `F = freeProP p (Fin n)` be the free pro-`p` group on `n` generators, let `r ∈ Φ(F)`, and let
`G ≅ ⟨x₁, …, x_n ∣ r⟩` be a Demushkin group. By Labute's criterion
(`TauCeti.IsDemushkin.nondegenerate_degreeOneForm`), the degree-one form of the class of `r` in
`gr_1(F)` is nondegenerate, and it is alternating exactly when every cup square `a ⌣ a` on
`H¹(G, 𝔽_p)` vanishes (`TauCeti.freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero`).
Feeding the relator through the normal forms of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm` gives Labute's normal
forms modulo `λ_2(F)`: when every cup square on `H¹(G, 𝔽_p)` vanishes, a change of basis of `F`
brings `r` to `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` modulo `λ_2(F)` with `q ∈ {0, p}`, and `n` is even;
when some cup square does not vanish, which forces `p = 2`, it brings `r` to
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` for odd `n` and to
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` for even `n`.

## Main results

* `TauCeti.IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo`,
  `TauCeti.IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOdd`,
  `TauCeti.IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven`:
  **Labute's normal forms modulo `λ_2(F)` for the relator of a Demushkin group**, according to
  whether the cup form on `H¹(G, 𝔽_p)` is alternating or not.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Propositions 3 and 4.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
-/

public section

namespace TauCeti

universe v

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the
-- nondegeneracy hypotheses below are stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

section NormalForm

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {r : freeProP p (Fin n)}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (hr : r ∈ proPFrattini p (freeProP p (Fin n))) (e : presentedProP p (Fin n) {r} ≃ₜ* G)
  (hG : IsDemushkin p G)
include hr e hG

/-- **Labute's normal form modulo `λ_2` for a Demushkin relator, the alternating case.** Let
`G ≅ ⟨x₁, …, x_n ∣ r⟩` with `r ∈ Φ(F)` be a Demushkin group on which every cup square
`a ⌣ a` vanishes, which for odd `p` is automatic. Then `n` is even, and a continuous automorphism
of `F` carries the class of `r` in `gr_1(F)` to the class of `(x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` or
to the class of `x₁^p (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`: after a change of basis,
`r ≡ x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n) mod λ_2(F)` with `q = 0` or `q = p`. -/
theorem IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo
    (halt : ∀ a : cohomFp p G 1, cupFp p G a a = 0) :
    Even n ∧ ∃ e' : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      gradedMap p (e' : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (e' : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1
          (gradedMk p (freeProP p (Fin n)) 1
            ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩) =
        gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo 0 n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one (dvd_zero p) n _⟩ ∨
      gradedMap p (e' : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (e' : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1
          (gradedMk p (freeProP p (Fin n)) 1
            ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩) =
        gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo p n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _⟩ :=
  freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo _
    (hG.nondegenerate_degreeOneForm hr e)
    ((freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero hr e).2 halt)

end NormalForm

section Dyadic

variable {n : ℕ} {r : freeProP 2 (Fin n)}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n))) (e : presentedProP 2 (Fin n) {r} ≃ₜ* G)
  (hG : IsDemushkin 2 G) (hnalt : ∃ a : cohomFp 2 G 1, cupFp 2 G a a ≠ 0)
include hr e hG hnalt

/-- **Labute's normal form modulo `λ_2` for a Demushkin relator, the nonalternating case of odd
rank.** Let `G ≅ ⟨x₁, …, x_n ∣ r⟩` with `r ∈ Φ(F)` be a Demushkin group at `p = 2` on which some
cup square `a ⌣ a` does not vanish, with `n` odd. Then for every `f ≥ 2` a continuous automorphism
of `F` carries the class of `r` in `gr_1(F)` to the class of
`x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)`. -/
theorem IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOdd
    (hn : Odd n) {f : ℕ} (hf : 2 ≤ f) :
    ∃ e' : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e' : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
          (e' : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
          (gradedMk 2 (freeProP 2 (Fin n)) 1
            ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le hr⟩) =
        gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoOdd f n (freeProPGen 2 n),
          demushkinWordTwoOdd_mem_pLowerCentralSeries_one (zero_lt_two.trans_le hf) n _⟩ :=
  freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoOdd _
    (hG.nondegenerate_degreeOneForm hr e)
    (fun h ↦ hnalt.elim fun a ha ↦
      ha ((freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero hr e).1 h a))
    hn hf

/-- **Labute's normal form modulo `λ_2` for a Demushkin relator, the nonalternating case of even
rank.** Let `G ≅ ⟨x₁, …, x_n ∣ r⟩` with `r ∈ Φ(F)` be a Demushkin group at `p = 2` on which some
cup square `a ⌣ a` does not vanish, with `n` even. Then for every `a` divisible by `4` and every
`f ≥ 2` a continuous automorphism of `F` carries the class of `r` in `gr_1(F)` to the class of
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem IsDemushkin.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven
    (hn : Even n) {a f : ℕ} (ha : 4 ∣ a) (hf : 2 ≤ f) :
    ∃ e' : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e' : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
          (e' : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
          (gradedMk 2 (freeProP 2 (Fin n)) 1
            ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le hr⟩) =
        gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven a f n (freeProPGen 2 n),
          demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_trans (Dvd.intro 2 rfl) ha)
            (zero_lt_two.trans_le hf) n _⟩ :=
  freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordTwoEven _
    (hG.nondegenerate_degreeOneForm hr e)
    (fun h ↦ hnalt.elim fun a ha ↦
      ha ((freeProP.isAlt_degreeOneForm_iff_forall_cupFp_self_eq_zero hr e).1 h a))
    hn ha hf

end Dyadic

end TauCeti
