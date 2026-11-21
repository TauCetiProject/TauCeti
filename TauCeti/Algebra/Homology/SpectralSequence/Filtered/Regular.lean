/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.BoundedBelow
public import TauCeti.Algebra.Homology.SpectralObject.Regular
public import TauCeti.Algebra.Homology.ModuleCat.Cokernel
public import TauCeti.Algebra.Homology.ModuleCat.Subobject
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

/-!
# Weak convergence of the regular spectral sequence of a complete filtration

Let `F` be an increasing filtration of a cochain complex of modules `K`, with spectral sequence
`E`, and let `n = p + q`. The object at `(p, q)` on page `r` is
`E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`, the image of `H^n(F_{q+1}/F_{q-r+2})` in
`H^n(F_{q+r-1}/F_q)`. Its representatives in `H^n(F_{q+1}/F_q)` that come from
`H^n(F_{q+1}/F_{q-r+2})` are the cycles `Z_r` of page `r`. The graded piece
`F_{q+1} H^n / F_q H^n` of the abutment is `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`), whose representatives are the
*permanent cycles*, the classes that come from `H^n(F_{q+1})` itself. When `F` is not bounded below,
the permanent cycles can be strictly fewer than the classes lying in every `Z_r`. This file shows
that they are not when the filtration is complete and the spectral sequence is regular, which is
the weak convergence part of Weibel's Complete Convergence Theorem 5.5.10.

The spectral sequence is *regular* at `(n - t, t)` from `i₀` on when the cycles `Z_r` at that
position are the same on all pages `r ≥ t - i₀ + 2`
(`CategoryTheory.Abelian.SpectralObject.IsRegularAt`, in
`TauCeti.Algebra.Homology.SpectralObject.Regular`). This holds as soon as the differentials
leaving the object at `(n - t, t)` vanish on all late enough pages, which is Weibel's definition
of regularity (`CategoryTheory.Abelian.SpectralObject.isRegularAt_of_page_d_eq_zero`). The proof
of weak convergence has two steps.

* **Mittag-Leffler.** Regularity at every position `t ≤ q` makes the tower of the modules
  `H^n(F_{q+1}/F_s)`, `s ≤ q`, Mittag-Leffler
  (`CategoryTheory.Abelian.SpectralObject.exists_rangeStableFrom_of_isRegularAt`). So a class of
  `H^n(F_{q+1}/F_q)` lying in every `Z_r` extends to a compatible family of classes of all the
  `H^n(F_{q+1}/F_s)`
  (`CategoryTheory.Abelian.SpectralObject.exists_compatible_family_of_forall_mem_range`).
* **Completeness.** If the stages `F_{q+1-k}` form a complete filtration of `K^n` and the
  filtration of `K^{n+1}` is separated, a compatible family of classes of the `H^n(F_{q+1}/F_s)`
  comes from `H^n(F_{q+1})`
  (`CochainComplex.exists_spectralObject_H_map_eq_of_isCompleteFiltration`).
  This is the surjectivity of `H^n(lim) ⟶ lim H^n` for the tower of quotients, proved by
  successive approximation of cocycle representatives.

Together, the permanent cycles are the cycles of all late enough pages
(`CochainComplex.exists_spectralObject_H_map_eq_of_isRegularAt`), so the canonical maps
`E^n(⊥ ≤ q ≤ q + 1 ≤ j) ⟶ E^n(i ≤ q ≤ q + 1 ≤ j)` are isomorphisms for `i` small enough
(`CochainComplex.isIso_mapFourδ₁Toδ₀'_of_isRegularAt`). For a filtration, the object at `(p, q)` on
every late enough page `r` is therefore `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`
(`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`) and maps onto the graded piece
`F_{q+1} H^n / F_q H^n` (`CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular`). When
the filtration is moreover exhaustive in degree `n - 1`, an element vanishes in the graded piece
exactly when it vanishes on some later page
(`CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular_eq_zero_iff`): the graded piece
is the direct limit of the pages, which is weak convergence. No boundedness of the filtration is
assumed in any degree; the strong convergence statements of
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete` need in addition the vanishing of the
graded cohomology beyond a bound.

## Main definitions

* `CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`,
  `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular`: the late pages of a regular
  spectral sequence of a complete filtration, and their epimorphisms onto the graded pieces.

## Main results

* `CochainComplex.exists_spectralObject_H_map_eq_of_isCompleteFiltration`: compatible classes of
  the quotients of a complete filtration lift.
* `CochainComplex.isIso_mapFourδ₁Toδ₀'_of_isRegularAt`: for a complete filtration with regular
  spectral sequence, the permanent cycles are the cycles of the late pages.
* `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular_eq_zero_iff`: **weak
  convergence** of the regular spectral sequence of a complete exhaustive filtration.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, §3.5 (towers and the Mittag-Leffler
  condition), §5.2 (regular and weakly convergent spectral sequences) and Theorem 5.5.10.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CochainComplex

universe v

variable {R : Type*} [Ring R]

section Functor

variable (G : EInt ⥤ CochainComplex (ModuleCat.{v} R) ℤ)

/-- The maps between the quotients `G_a / G_s` induced by `G`, on homology classes of
representatives in `G_a`. -/
private lemma homologyMap_cokernelMap_moduleCatKerHomologyClass {s s' a : EInt} (f : s ⟶ a)
    (g : s' ⟶ a)
    (u : s ⟶ s') (v : a ⟶ a) (w : G.map u ≫ G.map g = G.map f ≫ G.map v) (n : ℤ)
    (y : (G.obj a).X n)
    (hy : ((cokernel (G.map f)).d n (n + 1)) ((cokernel.π (G.map f)).f n y) = 0)
    (hy' : ((cokernel (G.map g)).d n (n + 1)) ((cokernel.π (G.map g)).f n y) = 0) :
    HomologicalComplex.homologyMap (cokernel.map (G.map f) (G.map g) (G.map u) (G.map v) w) n
        ((cokernel (G.map f)).moduleCatKerHomologyClass (CochainComplex.next ℤ n)
          ⟨(cokernel.π (G.map f)).f n y, hy⟩) =
      (cokernel (G.map g)).moduleCatKerHomologyClass (CochainComplex.next ℤ n)
        ⟨(cokernel.π (G.map g)).f n y, hy'⟩ := by
  obtain rfl : v = 𝟙 a := Subsingleton.elim _ _
  convert HomologicalComplex.homologyMap_cokernel_map_moduleCatKerHomologyClass _ _ _ _ w _ y hy
    (by simpa using hy') using 3 <;> simp

/-- The cochain `c` of `G_a` represents the class `ξ` of `H^n(G_a / G_s)`. -/
private def IsCokernelRep {s a : EInt} (f : s ⟶ a) {n : ℤ}
    (ξ : (cokernel (G.map f)).homology n) (c : (G.obj a).X n) : Prop :=
  ∃ hc : ((cokernel (G.map f)).d n (n + 1)) ((cokernel.π (G.map f)).f n c) = 0,
    (cokernel (G.map f)).moduleCatKerHomologyClass (CochainComplex.next ℤ n) ⟨_, hc⟩ = ξ

private lemma exists_isCokernelRep {s a : EInt} (f : s ⟶ a) {n : ℤ}
    (ξ : (cokernel (G.map f)).homology n) : ∃ c, IsCokernelRep G f ξ c := by
  obtain ⟨⟨z, hz⟩, hzξ⟩ := HomologicalComplex.moduleCatKerHomologyClass_surjective _ _ ξ
  obtain ⟨c, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ n z
  exact ⟨c, hz, hzξ⟩

/-- Let `s' ≤ s ≤ a`, and let `ξ` be the image of a class `ξ'` of `H^n(G_a / G_{s'})` in
`H^n(G_a / G_s)`. A representative of `ξ` is corrected by an element of `G_s` to a representative
of `ξ'`. -/
private lemma exists_isCokernelRep_sub_mem_range {s' s a : EInt} (f' : s' ⟶ a) (f : s ⟶ a)
    (u : s' ⟶ s) {n : ℤ} (ξ' : (cokernel (G.map f')).homology n)
    (ξ : (cokernel (G.map f)).homology n)
    (hξ : HomologicalComplex.homologyMap (cokernel.map (G.map f') (G.map f) (G.map u)
      (G.map (𝟙 a)) (G.map_comp_map_eq_map_comp_map _ _ _ _)) n ξ' = ξ)
    (c : (G.obj a).X n) (hc : IsCokernelRep G f ξ c) :
    ∃ c', IsCokernelRep G f' ξ' c' ∧ c' - c ∈ LinearMap.range ((G.map f).f n).hom := by
  obtain ⟨c', hc'₁, hc'₂⟩ := exists_isCokernelRep G f' ξ'
  -- `c'` also represents `ξ` modulo `G_s`, so it differs from `c` by a boundary modulo `G_s`.
  have hc'₃ := (HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff (G.map f) n (n + 1) c').2
    (HomologicalComplex.range_map_f_le G _ _ u _
      ((HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff _ n (n + 1) c').1 hc'₁))
  obtain ⟨e, he⟩ := HomologicalComplex.exists_sub_sub_d_mem_range_of_moduleCatKerHomologyClass_eq
    _ (CochainComplex.next ℤ n) (CochainComplex.prev ℤ n) c' c hc'₃ hc.1 (by
      rw [← homologyMap_cokernelMap_moduleCatKerHomologyClass G _ _ u (𝟙 _)
        (G.map_comp_map_eq_map_comp_map _ _ _ _) n c' hc'₁ hc'₃, hc'₂, hξ, hc.2])
  have h₁ : ((cokernel (G.map f')).d n (n + 1))
      ((cokernel.π (G.map f')).f n (c' - (G.obj a).d (n - 1) n e)) = 0 := by
    rw [HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff, map_sub,
      HomologicalComplex.d_comp_d_apply, sub_zero]
    exact (HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff _ n (n + 1) c').1 hc'₁
  exact ⟨c' - (G.obj a).d (n - 1) n e,
    ⟨h₁, by rw [HomologicalComplex.moduleCatKerHomologyClass_cokernel_π_sub_d _
      (CochainComplex.next ℤ n) (CochainComplex.prev ℤ n) c' e h₁ hc'₁, hc'₂]⟩,
    by rwa [sub_right_comm]⟩

/-- The form of `CochainComplex.exists_spectralObject_H_map_eq_of_isCompleteFiltration` for the
cohomology of the quotients `G_a / G_s`. The proof is by successive approximation: the
representatives in `G_a` of the classes are corrected step by step so that consecutive ones agree
modulo deeper and deeper stages, and their limit is a cocycle of `G_a` representing all of them. -/
private theorem exists_homologyMap_cokernelMap_eq {a n : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f n).hom)
    (hs : ∀ y : (G.obj a).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f (n + 1)).hom) →
        y = 0)
    (ξ : ∀ (s : ℤ) (hs : s ≤ a),
      (cokernel (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).homology n)
    (hξ : ∀ (s s' : ℤ) (h : s ≤ s') (h' : s' ≤ a) (u : (s : EInt) ⟶ s') (v : (a : EInt) ⟶ a) w,
      HomologicalComplex.homologyMap (cokernel.map
        (G.map (homOfLE (WithBotTop.coe_le_coe.2 (h.trans h'))))
        (G.map (homOfLE (WithBotTop.coe_le_coe.2 h'))) (G.map u) (G.map v) w) n
          (ξ s (h.trans h')) = ξ s' h') :
    ∃ y : (cokernel (G.map (homOfLE (bot_le : (⊥ : EInt) ≤ a)))).homology n,
      ∀ (s : ℤ) (hs : s ≤ a) (u : (⊥ : EInt) ⟶ s) (v : (a : EInt) ⟶ a) w,
        HomologicalComplex.homologyMap (cokernel.map (G.map (homOfLE bot_le))
          (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs))) (G.map u) (G.map v) w) n y =
          ξ s hs := by
  -- `Rep k c`: the cochain `c` of `G_a` represents `ξ (a - k)` modulo `G_{a-k}`.
  let Rep (k : ℕ) (c : (G.obj a).X n) : Prop :=
    IsCokernelRep G (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))
      (ξ (a - k) (by omega)) c
  have step (k : ℕ) (c) (hc : Rep k c) : ∃ c', Rep (k + 1) c' ∧ c' - c ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f n).hom :=
    exists_isCokernelRep_sub_mem_range G _ _
      (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - (k + 1 : ℕ) ≤ a - k))) _ _
      (hξ _ _ (by omega) _ _ _ _) c hc
  obtain ⟨c₀, hc₀⟩ := exists_isCokernelRep G _ (ξ (a - (0 : ℕ)) (by omega))
  -- The successive representatives, and their limit `L` in `G_a`.
  choose next hnext using step
  obtain ⟨seq, -, hseqs⟩ : ∃ seq : (k : ℕ) → {c // Rep k c}, (seq 0).val = c₀ ∧
      ∀ k, (seq (k + 1)).val = next k (seq k).val (seq k).property :=
    ⟨fun k ↦ Nat.rec ⟨c₀, hc₀⟩
      (fun k c ↦ ⟨next k c.val c.property, (hnext k c.val c.property).1⟩) k, rfl, fun _ ↦ rfl⟩
  obtain ⟨L, hL⟩ := hc.exists_limit (fun k ↦ (seq k).val) fun k ↦ by
    rw [hseqs]
    exact (hnext k _ _).2
  -- `L` is a cocycle: its boundary lies in every `G_{a-k}`.
  have hdL : (G.obj a).d n (n + 1) L = 0 := hs _ fun k ↦ by
    rw [← sub_add_cancel L (seq k).val, map_add]
    refine add_mem ?_
      ((HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff _ n (n + 1) _).1 (seq k).property.1)
    obtain ⟨z, hz⟩ := hL k
    exact ⟨(G.obj _).d n (n + 1) z, by rw [← HomologicalComplex.Hom.comm_apply, hz]⟩
  have hL₀ : ((cokernel (G.map (homOfLE (bot_le : (⊥ : EInt) ≤ a)))).d n (n + 1))
      ((cokernel.π (G.map (homOfLE (bot_le : (⊥ : EInt) ≤ a)))).f n L) = 0 := by
    rw [HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff, hdL]
    exact zero_mem _
  refine ⟨HomologicalComplex.moduleCatKerHomologyClass _ (CochainComplex.next ℤ n) ⟨_, hL₀⟩,
    fun s hs u v w ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = a - k := ⟨(a - s).toNat, by omega⟩
  -- Modulo `G_{a-k}`, `L` and the `k`th representative agree.
  have hLk : (cokernel.π (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).f n L =
      (cokernel.π (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).f n (seq k).val := by
    rw [← sub_eq_zero, ← map_sub, HomologicalComplex.cokernel_π_f_apply_eq_zero_iff]
    exact hL k
  have hLk' : ((cokernel (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).d n (n + 1))
      ((cokernel.π (G.map (homOfLE (WithBotTop.coe_le_coe.2 hs)))).f n L) = 0 := by
    rw [hLk]
    exact (seq k).property.1
  rw [homologyMap_cokernelMap_moduleCatKerHomologyClass G _ _ u v w n L hL₀ hLk',
    ← (seq k).property.2]
  congr 2

variable [∀ {a b : EInt} (f : a ⟶ b), Mono (G.map f)]

/-- **Compatible classes of the quotients of a complete filtration lift.** Let `G` have monomorphic
transition maps, and suppose that the stages `G_{a-k}` cut out a complete filtration of `G_a^n` and
a separated filtration of `G_a^{n+1}`. Then a family of classes `x s ∈ H^n(s ≤ a)`, `s ≤ a`, of the
quotients `G_a / G_s`, compatible under the maps `H^n(s ≤ a) ⟶ H^n(s' ≤ a)`, is the image of a
single class of `H^n(⊥ ≤ a)`. This is the surjectivity of `H^n(lim) ⟶ lim H^n` for the tower of
quotients of `G_a`, whose limit is `G_a` by completeness. -/
theorem exists_spectralObject_H_map_eq_of_isCompleteFiltration {a n : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f n).hom)
    (hs : ∀ y : (G.obj a).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f (n + 1)).hom) →
        y = 0)
    (x : ∀ (s : ℤ) (hs : s ≤ a),
      ((spectralObject G).H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2 hs))))
    (hx : ∀ (s s' : ℤ) (h : s ≤ s') (h' : s' ≤ a),
      ((spectralObject G).H n).map (twoδ₁Toδ₀' (s : EInt) (s' : EInt) (a : EInt)
        (WithBotTop.coe_le_coe.2 h) (WithBotTop.coe_le_coe.2 h')) (x s (h.trans h')) = x s' h') :
    ∃ y : ((spectralObject G).H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a))),
      ∀ (s : ℤ) (hs : s ≤ a), ((spectralObject G).H n).map (twoδ₁Toδ₀' ⊥ (s : EInt) (a : EInt)
        bot_le (WithBotTop.coe_le_coe.2 hs)) y = x s hs := by
  obtain ⟨y, hy⟩ := exists_homologyMap_cokernelMap_eq G hc hs
    (fun s hs ↦ (spectralObjectHIsoCokernel G _ n).hom (x s hs)) fun s s' h h' u v w ↦ by
      -- `u` and `v` are the components of the morphism of arrows `twoδ₁Toδ₀'`.
      obtain rfl : u = (twoδ₁Toδ₀' (s : EInt) (s' : EInt) (a : EInt) (WithBotTop.coe_le_coe.2 h)
        (WithBotTop.coe_le_coe.2 h')).app 0 := Subsingleton.elim _ _
      obtain rfl : v = (twoδ₁Toδ₀' (s : EInt) (s' : EInt) (a : EInt) (WithBotTop.coe_le_coe.2 h)
        (WithBotTop.coe_le_coe.2 h')).app 1 := Subsingleton.elim _ _
      rw [← hx s s' h h', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom]
  refine ⟨(spectralObjectHIsoCokernel G _ n).inv y, fun s hs ↦
    (ModuleCat.mono_iff_injective (spectralObjectHIsoCokernel G _ n).hom).1 inferInstance ?_⟩
  rw [← ConcreteCategory.comp_apply, spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact hy s hs _ _ _

/-- **Permanent cycles of a regular spectral sequence of a complete filtration.** Suppose that the
stages `G_{q+1-k}` cut out a complete filtration of `G_{q+1}^n` and a separated filtration of
`G_{q+1}^{n+1}`, and that the spectral sequence is regular in total degree `n` at the position `q`
from `i₀` on and at every position `t < q`. Then for `i ≤ i₀`, every class of `H^n(q ≤ q + 1)`
coming from `H^n(i ≤ q + 1)` comes from `H^n(⊥ ≤ q + 1)`: the cycles of the object at
`(n - q, q)` on the pages `r ≥ q - i₀ + 2` are permanent cycles. -/
theorem exists_spectralObject_H_map_eq_of_isRegularAt {q n i₀ : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f n).hom)
    (hs : ∀ y : (G.obj ((q + 1 : ℤ) : EInt)).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f
        (n + 1)).hom) → y = 0)
    (hq : (spectralObject G).IsRegularAt n q i₀)
    (hreg : ∀ t < q, ∃ i₁, (spectralObject G).IsRegularAt n t i₁)
    (i : ℤ) (hi : i ≤ i₀)
    (w : ((spectralObject G).H n).obj (mk₁ (homOfLE (WithBotTop.coe_le_coe.2
      (by have := hq.le; omega : i ≤ q + 1))))) :
    ∃ y : ((spectralObject G).H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt)))),
      ((spectralObject G).H n).map (twoδ₁Toδ₀' ⊥ (q : EInt) ((q + 1 : ℤ) : EInt) bot_le
        (WithBotTop.coe_le_coe.2 (by omega))) y =
      ((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
        (WithBotTop.coe_le_coe.2 (by have := hq.le; omega))
        (WithBotTop.coe_le_coe.2 (by omega))) w := by
  have hi₀ := hq.le
  -- The tower `s ↦ H^n(s ≤ q + 1)` is Mittag-Leffler.
  have hml (s : ℤ) (hs : s ≤ q) := (spectralObject G).exists_rangeStableFrom_of_isRegularAt hs
    fun t _ ht ↦ (eq_or_lt_of_le ht).elim (fun h ↦ h ▸ ⟨i₀, hq⟩) (hreg t)
  obtain ⟨x, hx, hxq⟩ := (spectralObject G).exists_compatible_family_of_forall_mem_range hml
    (((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega))) w)
    fun i' hi' ↦ by
      rcases le_or_gt i i' with hii' | hii'
      · exact ⟨((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt) (i' : EInt)
          ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hii') (WithBotTop.coe_le_coe.2 (by omega)))
          w, (spectralObject G).H_map_map_apply _ _ _ w⟩
      · exact hq.range_le i' (by omega) ⟨((spectralObject G).H n).map (twoδ₁Toδ₀' (i : EInt)
          (i₀ : EInt) ((q + 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 hi)
          (WithBotTop.coe_le_coe.2 (by omega))) w, (spectralObject G).H_map_map_apply _ _ _ w⟩
  obtain ⟨y, hy⟩ := exists_spectralObject_H_map_eq_of_isCompleteFiltration G hc hs x hx
  exact ⟨y, (hy q (by omega)).trans hxq⟩

/-- **The late pages of a regular spectral sequence of a complete filtration.** Under the
hypotheses of `CochainComplex.exists_spectralObject_H_map_eq_of_isRegularAt`, for `i ≤ i₀` and
`q + 1 ≤ j` the canonical map `E^n(⊥ ≤ q ≤ q + 1 ≤ j) ⟶ E^n(i ≤ q ≤ q + 1 ≤ j)` is an isomorphism.
For `i = q - r + 2` and `j = q + r - 1`, its target is the object at `(n - q, q)` on page `r`. -/
theorem isIso_mapFourδ₁Toδ₀'_of_isRegularAt {q n i₀ : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f n).hom)
    (hs : ∀ y : (G.obj ((q + 1 : ℤ) : EInt)).X (n + 1), (∀ k : ℕ, y ∈ LinearMap.range
      ((G.map (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q + 1 - k ≤ q + 1)))).f
        (n + 1)).hom) → y = 0)
    (hq : (spectralObject G).IsRegularAt n q i₀)
    (hreg : ∀ t < q, ∃ i₁, (spectralObject G).IsRegularAt n t i₁)
    (i : ℤ) (hi : i ≤ i₀) (j : EInt) (hj : ((q + 1 : ℤ) : EInt) ≤ j) :
    IsIso ((spectralObject G).mapFourδ₁Toδ₀' ⊥ (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) j bot_le
      (WithBotTop.coe_le_coe.2 (by have := hq.le; omega)) (WithBotTop.coe_le_coe.2 (by omega)) hj
      (n - 1) n (n + 1)) := by
  have hi₀ := hq.le
  have := (spectralObject G).mono_map (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q)))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (fourδ₁Toδ₀' ⊥ (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) j bot_le
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)) hj) (n - 1) n
      (n + 1)
  refine (isIso_iff_mono_and_epi _).2 ⟨this, (ModuleCat.epi_iff_surjective _).2 fun e ↦ ?_⟩
  -- Write `e` through a representative `w ∈ H^n(i ≤ q + 1)`, and lift it to `H^n(⊥ ≤ q + 1)`.
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective ((spectralObject G).toE
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q)))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q + 1))) rfl (n - 1) n (n + 1))).1
    inferInstance e
  obtain ⟨y, hy⟩ := exists_spectralObject_H_map_eq_of_isRegularAt G hc hs hq hreg i hi w
  refine ⟨(spectralObject G).toE (homOfLE (bot_le : (⊥ : EInt) ≤ q))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (homOfLE bot_le) rfl (n - 1) n (n + 1) (by omega) (by omega) y, ?_⟩
  -- Compare the two elements through their images in `H^n(q ≤ j)`.
  apply (ModuleCat.mono_iff_injective ((spectralObject G).fromE
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q)))
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))) (homOfLE hj)
    (homOfLE ((WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1)).trans hj)) rfl
    (n - 1) n (n + 1))).1 inferInstance
  -- The arrows `q ≤ q + 1 ≤ j` and `q ≤ j`, shared by both objects.
  let f₂ := homOfLE (WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1))
  let f₂₃ := homOfLE ((WithBotTop.coe_le_coe.2 (by omega : q ≤ q + 1)).trans hj)
  have h₁ := ConcreteCategory.congr_hom ((spectralObject G).map_fromE
    (homOfLE (bot_le : (⊥ : EInt) ≤ q)) f₂ (homOfLE hj) f₂₃ rfl
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q))) f₂ (homOfLE hj) f₂₃ rfl
    (fourδ₁Toδ₀' ⊥ (i : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) j bot_le
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)) hj) (n - 1) n
      (n + 1) (𝟙 _) (by cat_disch) (by cat_disch) (by omega) (by omega))
    ((spectralObject G).toE (homOfLE (bot_le : (⊥ : EInt) ≤ q)) f₂ (homOfLE hj)
      (homOfLE bot_le) rfl (n - 1) n (n + 1) (by omega) (by omega) y)
  have h₂ := ConcreteCategory.congr_hom ((spectralObject G).toE_fromE
    (homOfLE (bot_le : (⊥ : EInt) ≤ q)) f₂ (homOfLE hj) (homOfLE bot_le) rfl f₂₃ rfl
    (n - 1) n (n + 1) (by omega) (by omega)) y
  have h₃ := ConcreteCategory.congr_hom ((spectralObject G).toE_fromE
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q))) f₂ (homOfLE hj)
    (homOfLE (WithBotTop.coe_le_coe.2 (by omega : i ≤ q + 1))) rfl f₂₃ rfl
    (n - 1) n (n + 1) (by omega) (by omega)) w
  simp only [ConcreteCategory.comp_apply, CategoryTheory.Functor.map_id, ModuleCat.id_apply]
    at h₁ h₂ h₃
  rw [h₁, h₂, h₃, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply]
  exact congrArg _ hy

end Functor

section Filtration

variable {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : ℤ → Subobject K) (hF : Monotone F)

/-- Completeness of the stages `F_{a-k}` in `K^m` is completeness of their images in `G_a^m`. -/
lemma isCompleteFiltration_range_filtrationFunctor_map_f {a m : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f m).hom) :
    TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range
      (((filtrationFunctor F hF).map (homOfLE (WithBotTop.coe_le_coe.2
        (by omega : a - k ≤ a)))).f m).hom := by
  convert hc.comap ((filtrationFunctorArrow F hF a).f m).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance) ?_ using 1
  · funext k
    ext y
    exact mem_range_filtrationFunctor_map_f_iff F hF _ y
  · rintro _ ⟨u, rfl⟩
    refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF a).symm).f m
      ((Subobject.ofLE _ _ (hF (by omega : a - ((0 : ℕ) : ℤ) ≤ a))).f m u), ?_⟩
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      eqToHom_comp_filtrationFunctorArrow, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]

/-- Separatedness of the filtration of `K^m` gives separatedness of the stages `G_{a-k}` in
`G_a^m`. -/
lemma eq_zero_of_forall_mem_range_filtrationFunctor_map_f {a m : ℤ}
    (hs : ∀ x : K.X m, (∀ i, x ∈ LinearMap.range ((F i).arrow.f m).hom) → x = 0)
    (y : ((filtrationFunctor F hF).obj (a : EInt)).X m)
    (hy : ∀ k : ℕ, y ∈ LinearMap.range (((filtrationFunctor F hF).map
      (homOfLE (WithBotTop.coe_le_coe.2 (by omega : a - k ≤ a)))).f m).hom) :
    y = 0 := by
  apply (ModuleCat.mono_iff_injective ((filtrationFunctorArrow F hF a).f m)).1 inferInstance
  rw [map_zero]
  refine hs _ fun i ↦ Subobject.range_arrow_f_hom_le (hF (by omega : a - (a - i).toNat ≤ i)) m
    ((mem_range_filtrationFunctor_map_f_iff F hF _ y).1 (hy (a - i).toNat))

section Pages

variable (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) {i₀ : ℤ}
  (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
    LinearMap.range ((F (pq.2 + 1 - k)).arrow.f (pq.1 + pq.2)).hom)
  (hs : ∀ x : K.X (pq.1 + pq.2 + 1),
    (∀ i, x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 + 1)).hom) → x = 0)
  (hq : (spectralObject (filtrationFunctor F hF)).IsRegularAt (pq.1 + pq.2) pq.2 i₀)
  (hreg : ∀ t < pq.2,
    ∃ i₁, (spectralObject (filtrationFunctor F hF)).IsRegularAt (pq.1 + pq.2) t i₁)
  (hri : pq.2 - r + 2 ≤ i₀)

/-- **The late pages of the regular spectral sequence of a complete filtration.** Let
`pq = (p, q)` and `n = p + q`. Suppose that the stages `F_{q+1-k}` form a complete filtration of
`K^n`, that the filtration of `K^{n+1}` is separated, and that the spectral sequence is regular in
total degree `n` at the position `q` from `i₀` on and at every position `t < q`. Then on every
page `r ≥ 2` with `q - r + 2 ≤ i₀`, the object at `(p, q)` is `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`. -/
noncomputable def filtrationSpectralSequencePageXIsoEBotOfRegular :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      (spectralObject (filtrationFunctor F hF)).E (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2))
        (homOfLE (coe_le_coe_add_one pq.2))
        (homOfLE (WithBotTop.coe_le_coe.2 (by omega : pq.2 + 1 ≤ pq.2 + r - 1)))
        (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) (by omega) (by omega) :=
  have := isIso_mapFourδ₁Toδ₀'_of_isRegularAt (filtrationFunctor F hF)
    (isCompleteFiltration_range_filtrationFunctor_map_f F hF hc)
    (eq_zero_of_forall_mem_range_filtrationFunctor_map_f F hF hs) hq hreg (pq.2 - r + 2) hri
    ((pq.2 + r - 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.2 (by omega))
  (spectralObject _).spectralSequencePageXIso coreE₂Cohomological r hr pq
      ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega) (by omega) ≪≫
    (asIso ((spectralObject _).mapFourδ₁Toδ₀' ⊥ ((pq.2 - r + 2 : ℤ) : EInt) pq.2
      ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.2 (by have := hq.le; omega)) (coe_le_coe_add_one pq.2)
      (WithBotTop.coe_le_coe.2 (by omega)) (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1)
      _ _)).symm

/-- The inverse of `CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular` is the canonical
map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)` followed by the
identification of the latter with the page object. -/
lemma filtrationSpectralSequencePageXIsoEBotOfRegular_inv :
    (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).inv =
      (spectralObject _).mapFourδ₁Toδ₀' ⊥ ((pq.2 - r + 2 : ℤ) : EInt) pq.2
          ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt) bot_le
          (WithBotTop.coe_le_coe.2 (by have := hq.le; omega)) (coe_le_coe_add_one pq.2)
          (WithBotTop.coe_le_coe.2 (by omega)) (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1)
          (by omega) (by omega) ≫
        ((spectralObject _).spectralSequencePageXIso coreE₂Cohomological r hr pq
          ((pq.2 - r + 2 : ℤ) : EInt) pq.2 ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt)
          rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega)
          (by omega)).inv :=
  (rfl)

/-- **The late pages map onto the graded pieces.** Under the hypotheses of
`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`, the epimorphism from the object
at `(p, q)` on page `r` onto the graded piece `F_{q+1} H^n / F_q H^n` of the filtration of
`H^n(K)`, `n = p + q`, through `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`. -/
noncomputable def filtrationSpectralSequencePageXToGradedOfRegular :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ⟶
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom ≫
    (spectralObject _).mapFourδ₄Toδ₃' ⊥ (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt)
      ((pq.2 + r - 1 : ℤ) : EInt) ⊤
      bot_le (coe_le_coe_add_one pq.2) (WithBotTop.coe_le_coe.2 (by omega)) le_top
      (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) _ _ ≫
    ((spectralObject _).EInftyIsoCokernel _ _).hom

/-- `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular` is
`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular` followed by the canonical map
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` and the identification of the latter
with the graded piece. -/
lemma filtrationSpectralSequencePageXToGradedOfRegular_def :
    filtrationSpectralSequencePageXToGradedOfRegular F hF r hr pq hc hs hq hreg hri =
      (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom ≫
        (spectralObject _).mapFourδ₄Toδ₃' ⊥ (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt)
          ((pq.2 + r - 1 : ℤ) : EInt) ⊤ bot_le (coe_le_coe_add_one pq.2)
          (WithBotTop.coe_le_coe.2 (by omega)) le_top (pq.1 + pq.2 - 1) (pq.1 + pq.2)
          (pq.1 + pq.2 + 1) (by omega) (by omega) ≫
        ((spectralObject _).EInftyIsoCokernel _ _).hom :=
  (rfl)

instance :
    Epi (filtrationSpectralSequencePageXToGradedOfRegular F hF r hr pq hc hs hq hreg hri) := by
  rw [filtrationSpectralSequencePageXToGradedOfRegular_def]
  infer_instance

/-- **Weak convergence of the regular spectral sequence of a complete exhaustive filtration**
(Weibel, Theorem 5.5.10). Under the hypotheses of
`CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`, suppose also that every element
of `K^{n-1}` lies in some `F_i`, `n = p + q`. Then an element of the object at `(p, q)` on page `r`
vanishes in the graded piece `F_{q+1} H^n / F_q H^n` exactly when it vanishes on some later page
`r'`, under the canonical map `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + r' - 1)`
read through `CochainComplex.filtrationSpectralSequencePageXIsoEBotOfRegular`. With the surjectivity
of `CochainComplex.filtrationSpectralSequencePageXToGradedOfRegular`, the graded piece is the direct
limit of the objects at `(p, q)` on the late pages. -/
theorem filtrationSpectralSequencePageXToGradedOfRegular_eq_zero_iff
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (x : ((spectralSequence (filtrationFunctor F hF)).page r).X pq) :
    filtrationSpectralSequencePageXToGradedOfRegular F hF r hr pq hc hs hq hreg hri x = 0 ↔
      ∃ (r' : ℤ) (hrr' : r ≤ r'),
        (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r' (hr.trans hrr') pq hc hs hq hreg
          (by omega)).inv ((spectralObject (filtrationFunctor F hF)).mapFourδ₄Toδ₃' ⊥
            (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt)
            ((pq.2 + r - 1 : ℤ) : EInt) ((pq.2 + r' - 1 : ℤ) : EInt) bot_le
            (coe_le_coe_add_one pq.2) (WithBotTop.coe_le_coe.2 (by omega))
            (WithBotTop.coe_le_coe.2 (by omega)) (pq.1 + pq.2 - 1) (pq.1 + pq.2)
            (pq.1 + pq.2 + 1) _ _
            ((filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom
              x)) = 0 := by
  set x' := (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r hr pq hc hs hq hreg hri).hom x
  rw [filtrationSpectralSequencePageXToGradedOfRegular_def, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, (ModuleCat.mono_iff_injective
      ((spectralObject (filtrationFunctor F hF)).EInftyIsoCokernel _ _).hom).1 inferInstance
      |>.eq_iff' (map_zero _)]
  constructor
  · intro h
    obtain ⟨j', hj', h'⟩ := exists_mapFourδ₄Toδ₃'_eq_zero (filtrationFunctor F hF) (q := pq.2)
      (j := pq.2 + r - 1) (n := pq.1 + pq.2) (by omega) (exists_filtrationFunctor_map_f_eq F hF hex)
      x' h
    obtain ⟨r', rfl⟩ : ∃ r', j' = pq.2 + r' - 1 := ⟨j' - pq.2 + 1, by ring⟩
    exact ⟨r', by omega, by rw [h', map_zero]⟩
  · rintro ⟨r', hrr', h⟩
    rw [(ModuleCat.mono_iff_injective (filtrationSpectralSequencePageXIsoEBotOfRegular F hF r'
      (hr.trans hrr') pq hc hs hq hreg (by omega)).inv).1 inferInstance |>.eq_iff' (map_zero _)]
      at h
    have := ConcreteCategory.congr_hom
      ((spectralObject (filtrationFunctor F hF)).mapFourδ₄Toδ₃'_comp
      ⊥ (pq.2 : EInt) ((pq.2 + 1 : ℤ) : EInt) ((pq.2 + r - 1 : ℤ) : EInt)
      ((pq.2 + r' - 1 : ℤ) : EInt) ⊤ bot_le (coe_le_coe_add_one pq.2)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)) le_top
      (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1)) x'
    rw [ConcreteCategory.comp_apply, h, map_zero] at this
    exact this.symm

end Pages

end Filtration

end CochainComplex
