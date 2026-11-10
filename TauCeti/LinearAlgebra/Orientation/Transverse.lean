/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.Fin
public import TauCeti.LinearAlgebra.Orientation.Basis
public import TauCeti.LinearAlgebra.Orientation.ShortExact
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Ray

/-!
# The orientation of a hyperplane transverse to a vector

Let `V` be a vector space of dimension `k + 1` over a linearly ordered field, oriented by `o`, and
let `W` be a subspace of dimension `k` with a vector `v ∉ W`. Then `o` and `v` orient `W`
(`Orientation.transverse`): a basis `b` of `W` is positive exactly when `v, b 0, …, b (k - 1)` is
a positive basis of `V` (`Orientation.transverse_eq_orientation_iff`). This is how an orientation
of a manifold together with a transverse vector field orients a codimension-one subbundle of the
tangent bundle, such as the tangent field of a transversely oriented codimension-one foliation.
Placing `v` first follows the outward-normal-first convention for boundaries; placing it last
instead multiplies the induced orientation by `(-1)ᵏ`.

The orientation can also be tested against an arbitrary basis `e` of `V`: `b` is positive exactly
when the sign of the determinant `e.det (v, b 0, …, b (k - 1))` matches whether `o` is the
orientation of `e` (`Orientation.transverse_eq_orientation_iff_det`). This is the form in which
continuity of induced orientations is checked in local trivializations. The induced orientation
depends only on the class of `v` modulo `W` (`Orientation.transverse_congr`).

When `W` is the boundary hyperplane of a half-space and `v` points out of it, this is the
outward-first boundary orientation, and the second half of the file computes it for the two
constructions that orient fibre products. For a short exact sequence `0 → U → V → W → 0` oriented
subspace first, `[V] = [U][W]`, cutting `U` and `V` down to compatible hyperplanes `U'` and `V'`
gives the subspace-first orientation of `0 → U' → V' → W → 0`: informally,
`[v][U'] = [U]` implies `[f v][U'][W] = [U][W]` (`Orientation.transverse_shortExact`). For a product
`E × F`, the boundary of the first factor gives `[E][F] = [v][∂E][F]`
(`Orientation.transverse_prod_left`), while the boundary of the second factor costs the sign
`(-1) ^ dim E` of moving the outward vector past `E` (`Orientation.transverse_prod_right`).

## Main definitions

* `Orientation.transverse`: the orientation of `W` induced by an orientation of `V` and a vector
  `v ∉ W`.

## Main results

* `Orientation.transverse_eq_orientation_iff`: a basis `b` of `W` is positive exactly when the
  basis `v, b 0, …, b (k - 1)` of `V` is.
* `Orientation.transverse_eq_orientation_iff_det`: the same, read through the determinant with
  respect to any basis of `V`.
* `Orientation.transverse_neg`: reversing the orientation of `V` reverses the induced
  orientation.
* `Orientation.transverse_congr`: the induced orientation depends only on `v` modulo `W`.
* `Orientation.transverse_shortExact`: outward-first boundary orientations commute with
  subspace-first orientations of short exact sequences.
* `Orientation.transverse_prod_left`, `Orientation.transverse_prod_right`: the boundary
  orientation of a product along a hyperplane in either factor.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 15
  (orientations of hypersurfaces induced by a transverse vector field, Proposition 15.21).
-/

public section

noncomputable section

open Module

namespace Orientation

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V] {k : ℕ} {W : Submodule R V} {v : V}

/-- A basis of a subspace `W` of dimension `k` of a space `V` of dimension `k + 1`, the reference
basis against which `Orientation.transverse` is defined. -/
private def refBasis (hV : finrank R V = k + 1) (hW : finrank R W = k) : Basis (Fin k) R W :=
  haveI : FiniteDimensional R V := .of_finrank_eq_succ hV
  finBasisOfFinrankEq R W hW

variable [LinearOrder R] [IsStrictOrderedRing R] (o : Orientation R V (Fin (k + 1)))
  (hV : finrank R V = k + 1) (hW : finrank R W = k) (hv : v ∉ W)

open Classical in
/-- The orientation of a subspace `W` of dimension `k` of a space `V` of dimension `k + 1`
induced by an orientation `o` of `V` and a vector `v ∉ W`: a basis `b` of `W` is positive exactly
when `v, b 0, …, b (k - 1)` is a positive basis of `V`
(`Orientation.transverse_eq_orientation_iff`). -/
def transverse : Orientation R W (Fin k) :=
  if (Basis.mkFinConsOfNotMem v (refBasis hV hW) hv hV).orientation = o then
    (refBasis hV hW).orientation
  else -(refBasis hV hW).orientation

/-- **The transverse orientation is characterized by prepending the vector.** A basis `b` of `W`
is positive for the orientation induced by `o` and `v` exactly when the basis `c` of `V` with
`c = (v, b 0, …, b (k - 1))` is positive for `o`. -/
theorem transverse_eq_orientation_iff (b : Basis (Fin k) R W) (c : Basis (Fin (k + 1)) R V)
    (hc : ⇑c = Fin.cons v (W.subtype ∘ b)) :
    o.transverse hV hW hv = b.orientation ↔ c.orientation = o := by
  set b₀ := refBasis hV hW
  set c₀ := Basis.mkFinConsOfNotMem v b₀ hv hV
  -- `c` is positive for `c₀` exactly when `b` is positive for `b₀`.
  have hdet : c₀.det c = b₀.det b := by
    rw [hc]
    exact b₀.det_finCons_eq_det c₀ (Basis.coe_mkFinConsOfNotMem v b₀ hv hV) b
  have key : c₀.orientation = c.orientation ↔ b₀.orientation = b.orientation := by
    rw [c₀.orientation_eq_iff_det_pos, b₀.orientation_eq_iff_det_pos, hdet]
  rw [transverse]
  split_ifs with h
  · rw [← h, eq_comm (a := c.orientation), key]
  · obtain rfl : o = -c₀.orientation := (c₀.orientation_ne_iff_eq_neg o).1 (Ne.symm h)
    rw [eq_comm, ← b₀.orientation_ne_iff_eq_neg, ← c₀.orientation_ne_iff_eq_neg, ne_comm,
      ne_comm (a := c.orientation)]
    exact not_congr key.symm

/-- **The transverse orientation through determinants.** For any basis `e` of `V`, a basis `b` of
`W` is positive for the orientation induced by `o` and `v` exactly when the determinant
`e.det (v, b 0, …, b (k - 1))` is positive if `o` is the orientation of `e`, and negative
otherwise. -/
theorem transverse_eq_orientation_iff_det (b : Basis (Fin k) R W) (e : Basis (Fin (k + 1)) R V) :
    o.transverse hV hW hv = b.orientation ↔
      (o = e.orientation ↔ 0 < e.det (Fin.cons v (W.subtype ∘ b))) := by
  set c := Basis.mkFinConsOfNotMem v b hv hV
  have hc : ⇑c = Fin.cons v (W.subtype ∘ b) := Basis.coe_mkFinConsOfNotMem v b hv hV
  rw [transverse_eq_orientation_iff o hV hW hv b c hc, ← hc, ← e.orientation_eq_iff_det_pos]
  rcases e.orientation_eq_or_eq_neg o with rfl | rfl
  · simp only [true_iff]
    exact eq_comm
  · have hne : ¬(-e.orientation = e.orientation) := (Module.Ray.ne_neg_self _).symm
    simp only [hne, false_iff]
    rw [← e.orientation_ne_iff_eq_neg]
    exact ne_comm

/-- Reversing the orientation of `V` reverses the induced orientation of `W`. -/
@[simp]
theorem transverse_neg : (-o).transverse hV hW hv = -o.transverse hV hW hv := by
  set b := refBasis hV hW
  set c := Basis.mkFinConsOfNotMem v b hv hV
  have hc : ⇑c = Fin.cons v (W.subtype ∘ b) := Basis.coe_mkFinConsOfNotMem v b hv hV
  have hneg := transverse_eq_orientation_iff (-o) hV hW hv b c hc
  rcases b.orientation_eq_or_eq_neg (o.transverse hV hW hv) with h | h
  · -- `c` is positive for `o`, hence not for `-o`.
    have ho : c.orientation = o := (transverse_eq_orientation_iff o hV hW hv b c hc).1 h
    rw [h, ← b.orientation_ne_iff_eq_neg, ne_eq, hneg, ho]
    exact Module.Ray.ne_neg_self o
  · -- `c` is not positive for `o`, hence positive for `-o`.
    have ho : c.orientation ≠ o := fun ho ↦ Module.Ray.ne_neg_self b.orientation
      (((transverse_eq_orientation_iff o hV hW hv b c hc).2 ho).symm.trans h)
    have hc' : c.orientation = -o := by
      rcases c.orientation_eq_or_eq_neg o with h' | h'
      · exact absurd h'.symm ho
      · rw [h']
        exact (_root_.neg_neg c.orientation).symm
    rw [hneg.2 hc', h]
    exact (_root_.neg_neg b.orientation).symm

/-- Scaling the orientation of `V` by a unit scales the induced orientation of `W`. -/
@[simp]
theorem transverse_units_smul (u : Rˣ) :
    (u • o).transverse hV hW hv = u • o.transverse hV hW hv :=
  Module.Ray.units_smul_of_map_neg (F := (Orientation.transverse · hV hW hv))
    (transverse_neg · hV hW hv) u o

/-- The transverse orientation depends only on the class of the vector modulo `W`: two vectors
`v, v' ∉ W` with `v' - v ∈ W` induce the same orientation of `W`. -/
theorem transverse_congr {v' : V} (hv' : v' ∉ W) (hvv' : v' - v ∈ W) :
    o.transverse hV hW hv' = o.transverse hV hW hv := by
  have : FiniteDimensional R V := .of_finrank_eq_succ hV
  set b := finBasisOfFinrankEq R W hW
  set e := finBasisOfFinrankEq R V hV
  -- `v' - v` followed by a basis of `W` is linearly dependent, so `e.det` vanishes on it.
  have hzero : e.det (Fin.cons (v' - v) (W.subtype ∘ b)) = 0 := by
    refine e.det.map_linearDependent _ fun hli ↦ ?_
    refine (linearIndependent_finCons.1 hli).2 ?_
    rwa [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hdet : e.det (Fin.cons v' (W.subtype ∘ b)) = e.det (Fin.cons v (W.subtype ∘ b)) := by
    simpa only [AlternatingMap.coe_multilinearMap, add_sub_cancel, hzero, add_zero] using
      e.det.toMultilinearMap.cons_add (W.subtype ∘ b) v (v' - v)
  have key : o.transverse hV hW hv' = b.orientation ↔ o.transverse hV hW hv = b.orientation := by
    rw [transverse_eq_orientation_iff_det o hV hW hv' b e, hdet,
      ← transverse_eq_orientation_iff_det o hV hW hv b e]
  by_cases hb : o.transverse hV hW hv = b.orientation
  · rw [hb, key.2 hb]
  · rw [(b.orientation_ne_iff_eq_neg _).1 hb, (b.orientation_ne_iff_eq_neg _).1 (mt key.1 hb)]

end Orientation

namespace Orientation

/-! ### Short exact sequences -/

section ShortExact

variable {K U V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {f : U →ₗ[K] V} {g : V →ₗ[K] W} {a c : ℕ}
  [FiniteDimensional K U] [FiniteDimensional K W]
  {U' V' : Type*} [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V']
  [FiniteDimensional K U'] {f' : U' →ₗ[K] V'} {g' : V' →ₗ[K] W}

/-- **Outward-first boundary orientations of a short exact sequence.** Let
`0 → U → V → W → 0` and `0 → U' → V' → W → 0` be short exact sequences, and let `ι : U' → U`
and `J : V' → V` be injective maps commuting with them, whose images are hyperplanes. Let
`u ∈ U` lie outside the image of `ι`, and let `oU'` be the orientation of `U'` corresponding to
the orientation of the image of `ι` induced by `oU` and `u`. Then the orientation of the image of
`J` induced by the subspace-first orientation `[U][W]` of `V` and the vector `f u` corresponds to
the subspace-first orientation `[U'][W]` of `V'`. Informally, `[u][U'] = [U]` gives
`[f u][U'][W] = [U][W]`. -/
theorem transverse_shortExact (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hf' : Function.Injective f') (hfg' : Function.Exact f' g')
    (hg' : Function.Surjective g') {ι : U' →ₗ[K] U} {J : V' →ₗ[K] V} (hι : Function.Injective ι)
    (hJ : Function.Injective J) (hfι : f ∘ₗ ι = J ∘ₗ f') (hgJ : g ∘ₗ J = g') {u : U}
    (hu : u ∉ LinearMap.range ι) (hfu : f u ∉ LinearMap.range J)
    (oU : Orientation K U (Fin (a + 1))) (oU' : Orientation K U' (Fin a))
    (p : Orientation K W (Fin c)) (hU : finrank K U = a + 1) (hU' : finrank K U' = a)
    (hc : finrank K W = c) (hUι : finrank K (LinearMap.range ι) = a)
    (hV : finrank K V = a + c + 1) (hVJ : finrank K (LinearMap.range J) = a + c)
    (hoU : oU.transverse hU hUι hu = map (Fin a) (LinearEquiv.ofInjective ι hι) oU') :
    (reindex K V (finCongr (Nat.add_right_comm a 1 c)) (shortExact hf hfg hg oU p hU hc)).transverse
        hV hVJ hfu =
      map (Fin (a + c)) (LinearEquiv.ofInjective J hJ) (shortExact hf' hfg' hg' oU' p hU' hc) := by
  set b' := finBasisOfFinrankEq K U' hU'
  set e := finBasisOfFinrankEq K W hc
  -- It suffices to treat the case where `oU'` and `p` are the orientations of `b'` and `e`.
  suffices key : ∀ oU : Orientation K U (Fin (a + 1)),
      oU.transverse hU hUι hu = map (Fin a) (LinearEquiv.ofInjective ι hι) b'.orientation →
      (reindex K V (finCongr (Nat.add_right_comm a 1 c))
          (shortExact hf hfg hg oU e.orientation hU hc)).transverse hV hVJ hfu =
        map (Fin (a + c)) (LinearEquiv.ofInjective J hJ)
          (shortExact hf' hfg' hg' b'.orientation e.orientation hU' hc) by
    have hfin' : Fintype.card (Fin a) = finrank K U' := by rw [Fintype.card_fin, hU']
    rcases oU'.eq_or_eq_neg b'.orientation hfin' with rfl | rfl <;>
      rcases e.orientation_eq_or_eq_neg p with rfl | rfl
    · exact key oU hoU
    · rw [shortExact_neg_right, Orientation.reindex_neg, transverse_neg, key oU hoU,
        shortExact_neg_right, Orientation.map_neg]
    all_goals
      have hneg := key (-oU) (by rw [transverse_neg, hoU, Orientation.map_neg, Module.Ray.neg_neg])
      rw [shortExact_neg_left, Orientation.reindex_neg, transverse_neg] at hneg
      simp only [shortExact_neg_left, shortExact_neg_right, Orientation.reindex_neg, transverse_neg,
        Orientation.map_neg, ← hneg, Module.Ray.neg_neg]
  intro oU hoU
  set eι := LinearEquiv.ofInjective ι hι
  set eJ := LinearEquiv.ofInjective J hJ
  -- `oU` is the orientation of the basis `u, ι (b' 0), …, ι (b' (a - 1))` of `U`.
  set cU := Basis.mkFinConsOfNotMem u (b'.map eι) hu hU
  have hcU : ⇑cU = Fin.cons u ((LinearMap.range ι).subtype ∘ b'.map eι) :=
    Basis.coe_mkFinConsOfNotMem _ _ _ _
  obtain rfl : cU.orientation = oU :=
    (transverse_eq_orientation_iff oU hU hUι hu (b'.map eι) cU hcU).1
      (by rw [hoU, Basis.orientation_map])
  -- The subspace-first basis `B'` of `V'` built from `b'` and lifts `s` of `e`.
  choose s hs using fun j ↦ hg' (e j)
  set B' := (Basis.ofExactLift hf' hfg' b' e s hs).reindex finSumFinEquiv
  have hB'₁ (i : Fin a) : B' (Fin.castAdd c i) = f' (b' i) := by
    simp [B', Basis.ofExactLift_inl]
  have hB'₂ (j : Fin c) : g' (B' (Fin.natAdd a j)) = e j := by
    simp [B', Basis.ofExactLift_inr, hs]
  -- The basis `f u, J (B' 0), …` of `V` is subspace-first for the sequence through `U`.
  set B := Basis.mkFinConsOfNotMem (f u) (B'.map eJ) hfu hV
  have hB : ⇑B = Fin.cons (f u) ((LinearMap.range J).subtype ∘ B'.map eJ) :=
    Basis.coe_mkFinConsOfNotMem _ _ _ _
  have hB₁ (i : Fin (a + 1)) :
      B.reindex (finCongr (Nat.add_right_comm a c 1)) (Fin.castAdd c i) = f (cU i) := by
    induction i using Fin.cases with
    | zero =>
      have : (finCongr (Nat.add_right_comm a c 1)).symm (Fin.castAdd c 0) = 0 := Fin.ext (by simp)
      rw [Basis.reindex_apply, this, hB, hcU, Fin.cons_zero, Fin.cons_zero]
    | succ i =>
      have : (finCongr (Nat.add_right_comm a c 1)).symm (Fin.castAdd c i.succ) =
          (Fin.castAdd c i).succ := Fin.ext (by simp)
      rw [Basis.reindex_apply, this, hB, hcU, Fin.cons_succ, Fin.cons_succ]
      simpa [eJ, eι, hB'₁] using (LinearMap.congr_fun hfι (b' i)).symm
  have hB₂ (j : Fin c) :
      g (B.reindex (finCongr (Nat.add_right_comm a c 1)) (Fin.natAdd (a + 1) j)) = e j := by
    have : (finCongr (Nat.add_right_comm a c 1)).symm (Fin.natAdd (a + 1) j) =
        (Fin.natAdd a j).succ := Fin.ext (by simp; omega)
    rw [Basis.reindex_apply, this, hB]
    simpa [eJ, hB'₂] using LinearMap.congr_fun hgJ (B' (Fin.natAdd a j))
  have hreindex : (B.reindex (finCongr (Nat.add_right_comm a c 1))).reindex
      (finCongr (Nat.add_right_comm a 1 c)) = B :=
    Basis.eq_of_apply_eq fun i ↦ by simp
  rw [shortExact_basis_orientation hf hfg hg hU hc cU e _ hB₁ hB₂, ← Basis.orientation_reindex,
    hreindex, shortExact_basis_orientation hf' hfg' hg' hU' hc b' e B' hB'₁ hB'₂,
    ← Basis.orientation_map]
  exact (transverse_eq_orientation_iff _ hV hVJ hfu (B'.map eJ) B hB).2 rfl

end ShortExact

/-! ### Products -/

section Prod

variable {K E F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F] {m n k : ℕ}

/-- **The boundary of the first factor of a product.** Let `p` be a hyperplane in `E` and
`v ∈ E × F` with `v.1 ∉ p`. The orientation of `p × F` induced by the product orientation `[E][F]`
and the vector `v` is the product of the orientation of `p` induced by `[E]` and `v.1` with
`[F]`: informally `[E][F] = [v.1][p][F]`. -/
theorem transverse_prod_left {p : Submodule K E} {v : E × F} (hv₁ : v.1 ∉ p)
    (o : Orientation K E (Fin (m + 1))) (o' : Orientation K F (Fin n)) (hE : finrank K E = m + 1)
    (hp : finrank K p = m) (hF : finrank K F = n) (hk : m + n = k)
    (hV : finrank K (E × F) = k + 1)
    (hW : finrank K (LinearMap.range (p.subtype.prodMap (LinearMap.id : F →ₗ[K] F))) = k)
    (hv : v ∉ LinearMap.range (p.subtype.prodMap (LinearMap.id : F →ₗ[K] F))) :
    (reindex K (E × F) (finCongr (by omega)) (prod o o' hE hF)).transverse hV hW hv =
      map (Fin k) (LinearEquiv.ofInjective _
          (p.injective_subtype.prodMap Function.injective_id :
            Function.Injective (p.subtype.prodMap (LinearMap.id : F →ₗ[K] F))))
        (reindex K (p × F) (finCongr hk) (prod (o.transverse hE hp hv₁) o' hp hF)) := by
  subst hk
  set J := p.subtype.prodMap (LinearMap.id : F →ₗ[K] F)
  have hJ : Function.Injective J := p.injective_subtype.prodMap Function.injective_id
  set eJ := LinearEquiv.ofInjective J hJ
  set eP := finBasisOfFinrankEq K p hp
  set cE := Basis.mkFinConsOfNotMem v.1 eP hv₁ hE
  have hcE : ⇑cE = Fin.cons v.1 (p.subtype ∘ eP) := Basis.coe_mkFinConsOfNotMem _ _ _ _
  set eF := finBasisOfFinrankEq K F hF
  -- It suffices to treat the orientations of `cE` and `eF`.
  suffices key : (reindex K (E × F) (finCongr (Nat.add_right_comm m 1 n))
      (prod cE.orientation eF.orientation hE hF)).transverse hV hW hv =
        map (Fin (m + n)) eJ (reindex K (p × F) (finCongr rfl)
          (prod (cE.orientation.transverse hE hp hv₁) eF.orientation hp hF)) by
    rcases cE.orientation_eq_or_eq_neg o with rfl | rfl <;>
      rcases eF.orientation_eq_or_eq_neg o' with rfl | rfl <;>
      simp only [prod_neg_left, prod_neg_right, Orientation.reindex_neg, transverse_neg,
        Orientation.map_neg, Module.Ray.neg_neg, key]
  -- The product basis, reindexed, is `(v.1, 0)` followed by `J` of the product basis of `p × F`.
  set P' := (eP.prod eF).reindex finSumFinEquiv
  set P := ((cE.prod eF).reindex finSumFinEquiv).reindex (finCongr (Nat.add_right_comm m 1 n))
  have hv₀ : (v.1, (0 : F)) ∉ LinearMap.range J := by simpa [J] using hv₁
  have hP : ⇑P = Fin.cons (v.1, 0) ((LinearMap.range J).subtype ∘ P'.map eJ) := by
    rw [Basis.coe_prod_reindex_finSumFinEquiv_finCongr, hcE]
    congr 1
    funext i
    induction i using Fin.addCases <;> simp [P', eJ, J]
  have hvv₀ : v - (v.1, 0) ∈ LinearMap.range J := ⟨(0, v.2), by ext <;> simp [J]⟩
  rw [(transverse_eq_orientation_iff cE.orientation hE hp hv₁ eP cE hcE).2 rfl,
    prod_basis_orientation, prod_basis_orientation, finCongr_refl, Orientation.reindex_refl,
    Equiv.refl_apply, ← Basis.orientation_reindex, transverse_congr _ hV hW hv₀ hv hvv₀,
    ← Basis.orientation_map]
  exact (transverse_eq_orientation_iff _ hV hW hv₀ (P'.map eJ) P hP).2 rfl

/-- **The boundary of the second factor of a product.** Let `p` be a hyperplane in `F` and
`v ∈ E × F` with `v.2 ∉ p`. The orientation of `E × p` induced by the product orientation `[E][F]`
and the vector `v` is `(-1) ^ dim E` times the product of `[E]` with the orientation of `p` induced
by `[F]` and `v.2`: informally `[E][F] = [E][v.2][p] = (-1) ^ dim E [v.2][E][p]`. -/
theorem transverse_prod_right {p : Submodule K F} {v : E × F} (hv₂ : v.2 ∉ p)
    (o : Orientation K E (Fin m)) (o' : Orientation K F (Fin (n + 1))) (hE : finrank K E = m)
    (hF : finrank K F = n + 1) (hp : finrank K p = n) (hk : m + n = k)
    (hV : finrank K (E × F) = k + 1)
    (hW : finrank K (LinearMap.range ((LinearMap.id : E →ₗ[K] E).prodMap p.subtype)) = k)
    (hv : v ∉ LinearMap.range ((LinearMap.id : E →ₗ[K] E).prodMap p.subtype)) :
    (reindex K (E × F) (finCongr (by omega)) (prod o o' hE hF)).transverse hV hW hv =
      (-1 : Kˣ) ^ m • map (Fin k) (LinearEquiv.ofInjective _
          (Function.injective_id.prodMap p.injective_subtype :
            Function.Injective ((LinearMap.id : E →ₗ[K] E).prodMap p.subtype)))
        (reindex K (E × p) (finCongr hk) (prod o (o'.transverse hF hp hv₂) hE hp)) := by
  subst hk
  set J := (LinearMap.id : E →ₗ[K] E).prodMap p.subtype
  have hJ : Function.Injective J := Function.injective_id.prodMap p.injective_subtype
  set eJ := LinearEquiv.ofInjective J hJ
  set eE := finBasisOfFinrankEq K E hE
  set eP := finBasisOfFinrankEq K p hp
  set cF := Basis.mkFinConsOfNotMem v.2 eP hv₂ hF
  have hcF : ⇑cF = Fin.cons v.2 (p.subtype ∘ eP) := Basis.coe_mkFinConsOfNotMem _ _ _ _
  -- Here `m + (n + 1)` and `m + n + 1` agree definitionally, so both reindexings are trivial.
  simp only [finCongr_refl, Orientation.reindex_refl, Equiv.refl_apply]
  -- It suffices to treat the orientations of `eE` and `cF`.
  suffices key : (prod eE.orientation cF.orientation hE hF).transverse hV hW hv =
      (-1 : Kˣ) ^ m • map (Fin (m + n)) eJ
        (prod eE.orientation (cF.orientation.transverse hF hp hv₂) hE hp) by
    rcases eE.orientation_eq_or_eq_neg o with rfl | rfl <;>
      rcases cF.orientation_eq_or_eq_neg o' with rfl | rfl <;>
      simp only [prod_neg_left, prod_neg_right, transverse_neg, Orientation.map_neg,
        Module.Ray.units_smul_neg, Module.Ray.neg_neg, key]
  -- Moving `(0, v.2)` to the front of the product basis passes the `m` basis vectors of `E`.
  set P' := (eE.prod eP).reindex finSumFinEquiv
  set i₀ : Fin (m + n + 1) := ⟨m, by omega⟩
  set P := ((eE.prod cF).reindex finSumFinEquiv).reindex i₀.cycleRange
  have hv₀ : ((0 : E), v.2) ∉ LinearMap.range J := by simpa [J] using hv₂
  have hP : ⇑P = Fin.cons (0, v.2) ((LinearMap.range J).subtype ∘ P'.map eJ) := by
    rw [Basis.coe_prod_reindex_finSumFinEquiv_cycleRange, hcF]
    congr 1
    funext i
    induction i using Fin.addCases <;> simp [P', eJ, J]
  have hvv₀ : v - (0, v.2) ∈ LinearMap.range J := ⟨(v.1, 0), by ext <;> simp [J]⟩
  -- `P` is `(-1) ^ m` times the product basis.
  have hsign : P.orientation =
      (-1 : Kˣ) ^ m • ((eE.prod cF).reindex finSumFinEquiv).orientation := by
    rw [Basis.orientation_reindex, Orientation.reindex_perm, Fin.sign_cycleRange]
    simp [i₀]
  have hsq : ((-1 : Kˣ) ^ m) * (-1 : Kˣ) ^ m = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [(transverse_eq_orientation_iff cF.orientation hF hp hv₂ eP cF hcF).2 rfl,
    prod_basis_orientation, prod_basis_orientation,
    show ((eE.prod cF).reindex finSumFinEquiv).orientation = (-1 : Kˣ) ^ m • P.orientation by
      rw [hsign, smul_smul, hsq, one_smul],
    transverse_units_smul, transverse_congr _ hV hW hv₀ hv hvv₀, ← Basis.orientation_map]
  congr 1
  exact (transverse_eq_orientation_iff _ hV hW hv₀ (P'.map eJ) P hP).2 rfl

end Prod

end Orientation
