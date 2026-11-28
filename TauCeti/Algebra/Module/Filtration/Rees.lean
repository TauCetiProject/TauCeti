/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Filtration.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.Int.Interval

/-!
# The Rees module of a filtered module

Let `F : ℤ → Submodule R M` be an increasing filtration. Its Rees module is
`R_F M = ⊕_p F_p M z^p`, the module of Laurent polynomials `∑ m_p z^p` with coefficients in `M`
whose `p`-th coefficient lies in `F_p M`. This is Mathlib's submodule `Finsupp.submodule F` of
`ℤ →₀ M`, and the operations on it live in the namespace `TauCeti.ReesModule`: the Rees
parameter `z` acts by the shift `TauCeti.ReesModule.shift`, `(z x)_p = x_{p-1}`. A filtered map
`u` induces `TauCeti.ReesModule.map u`, applying `u` to every coefficient. Mathlib's
`Ideal.Filtration.submodule` is the analogous construction for decreasing `ℕ`-indexed `I`-adic
filtrations inside `PolynomialModule R M`; the filtrations here are increasing and indexed by `ℤ`,
so the Rees module consists of Laurent polynomials.

The Rees module interpolates between the module and its associated graded module:
specializing `z` to `1` recovers `M` when `F` is exhaustive, and specializing `z` to `0` gives
`gr^F M = ⊕_p F_p M / F_{p-1} M`. Strictness of a filtered map `u : (M, F) → (N, G)` between
increasing filtrations, with `F` exhaustive, becomes a torsion condition: `u` is strict exactly
when the cokernel of `R u : R_F M → R_G N` has no `z`-torsion. This cokernel is the cokernel
of graded modules, not the Rees module of the filtered cokernel. Likewise, a sequence of
filtered maps is exact at every filtration step exactly when its Rees sequence is exact. These
are the facts through which Saito's theory of Hodge modules treats strictness of filtered
`D`-modules by `z`-torsion of Rees modules.

## Main definitions

* `TauCeti.ReesModule.single F p`: the Rees monomial `m z^p` of an element `m ∈ F_p M`.
* `TauCeti.ReesModule.shift hF`: multiplication by the Rees parameter `z`.
* `TauCeti.ReesModule.map u hu`: the Rees map `R u` of a filtered linear map `u`.
* `TauCeti.ReesModule.evalOne F`: specialization at `z = 1`, `∑ m_p z^p ↦ ∑ m_p`.
* `TauCeti.ReesModule.symbol F`: specialization at `z = 0`, sending `∑ m_p z^p` to the classes of
  its coefficients in the graded pieces `TauCeti.GradedPiece F p`.

## Main results

* `TauCeti.ReesModule.ker_evalOne`, `TauCeti.ReesModule.range_evalOne`,
  `TauCeti.ReesModule.quotShiftSubIdEquiv`: `R_F M / (z - 1) R_F M ≅ M` for an exhaustive
  filtration.
* `TauCeti.ReesModule.ker_symbol`, `TauCeti.ReesModule.symbol_surjective`,
  `TauCeti.ReesModule.quotShiftEquiv`: `R_F M / z R_F M ≅ gr^F M`.
* `TauCeti.ReesModule.mem_range_map_iff`: an element of `R_G N` lies in the image of `R u`
  exactly when each coefficient lies in the image of the corresponding filtration step.
* `TauCeti.ReesModule.isStrict_iff_injective_mapQ_shift`: a filtered map between increasing
  filtrations, with exhaustive source filtration, is strict exactly when `z` acts injectively on
  the cokernel of its Rees map.
* `TauCeti.ReesModule.exact_map_iff`: a pair of filtered maps is exact on every filtration step
  exactly when the pair of Rees maps is exact.

## References

* M. Saito, *Modules de Hodge polarisables*, Publ. RIMS 24 (1988), §1.1 and §1.2.
* P. Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.1.
-/

public section

open scoped DirectSum

namespace TauCeti

section Semiring

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

variable {F : ℤ → Submodule R M} {G : ℤ → Submodule R N} {H : ℤ → Submodule R P}

namespace ReesModule

/-- The coefficients of an element of the Rees module lie in the filtration steps. -/
theorem coe_apply_mem (x : Finsupp.submodule F) (p : ℤ) : (x : ℤ →₀ M) p ∈ F p := x.property p

/-- Elements of the Rees module are equal when their coefficients are. -/
theorem ext {x y : Finsupp.submodule F} (h : ∀ p, (x : ℤ →₀ M) p = (y : ℤ →₀ M) p) : x = y :=
  Subtype.ext (Finsupp.ext h)

theorem ext_iff {x y : Finsupp.submodule F} : x = y ↔ ∀ p, (x : ℤ →₀ M) p = (y : ℤ →₀ M) p :=
  ⟨fun h _ ↦ h ▸ rfl, ext⟩

/-! ### Rees monomials -/

section Single

variable (F) in
/-- The Rees monomial `m z^p` of an element `m ∈ F_p M`. -/
noncomputable def single (p : ℤ) : F p →ₗ[R] Finsupp.submodule F :=
  (Finsupp.lsingle p ∘ₗ (F p).subtype).codRestrict _
    fun m ↦ (Finsupp.comap_lsingle_submodule F p).ge m.property

@[simp]
theorem coe_single (p : ℤ) (m : F p) : (single F p m : ℤ →₀ M) = Finsupp.single p (m : M) := by
  simp [single]

@[simp]
theorem single_eq_zero {p : ℤ} {m : F p} : single F p m = 0 ↔ m = 0 := by
  rw [← Submodule.coe_eq_zero, coe_single, Finsupp.single_eq_zero, Submodule.coe_eq_zero]

end Single

/-! ### The Rees parameter -/

section Shift

/-- Multiplication by the Rees parameter `z` on `R_F M`, sending `m z^p` to `m z^{p+1}`. -/
noncomputable def shift (hF : Monotone F) : Finsupp.submodule F →ₗ[R] Finsupp.submodule F :=
  (Finsupp.domLCongr (R := R) (M := M) (Equiv.addRight (1 : ℤ))).toLinearMap.restrict
    fun x hx ↦ (Finsupp.mem_submodule_iff _ _).mpr fun p ↦ by
      simpa [Finsupp.domLCongr_apply] using hF (show p + -1 ≤ p by omega) (hx (p + -1))

variable (hF : Monotone F)

/-- The underlying Laurent polynomial of `z x` is `x` reindexed along `p ↦ p + 1`. -/
theorem coe_shift (x : Finsupp.submodule F) :
    (shift hF x : ℤ →₀ M) = Finsupp.domLCongr (R := R) (Equiv.addRight (1 : ℤ)) (x : ℤ →₀ M) :=
  LinearMap.coe_restrict_apply _ _

@[simp]
theorem coe_shift_apply (x : Finsupp.submodule F) (p : ℤ) :
    (shift hF x : ℤ →₀ M) p = (x : ℤ →₀ M) (p - 1) := by
  simp [shift, Finsupp.domLCongr_apply, sub_eq_add_neg]

/-- Multiplication by `z` sends the monomial `m z^p` to `m z^{p+1}`. -/
@[simp]
theorem shift_single (p : ℤ) (m : F p) :
    shift hF (single F p m) = single F (p + 1) ⟨m, hF (Int.le_add_one le_rfl) m.property⟩ := by
  ext q
  simp [Finsupp.single_apply, eq_sub_iff_add_eq]

/-- An element of `R_F M` is divisible by `z` exactly when each coefficient `m_p` lies in
`F_{p-1} M`. -/
theorem mem_range_shift_iff {x : Finsupp.submodule F} :
    x ∈ LinearMap.range (shift hF) ↔ ∀ p, (x : ℤ →₀ M) p ∈ F (p - 1) := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩ p
    simpa using y.property (p - 1)
  · let y : ℤ →₀ M := Finsupp.domLCongr (R := R) (Equiv.addRight (1 : ℤ)).symm (x : ℤ →₀ M)
    have hy : y ∈ Finsupp.submodule F := fun p ↦ by
      simpa [y, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply] using hx (p + 1)
    exact ⟨⟨y, hy⟩, by
      rw [ext_iff]
      intro p
      simp [y, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]⟩

end Shift

/-! ### Rees maps -/

section Map

/-- The Rees map `R u : R_F M → R_G N` of a filtered map `u`, applying `u` to each
coefficient. -/
noncomputable def map (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) :
    Finsupp.submodule F →ₗ[R] Finsupp.submodule G :=
  (Finsupp.mapRange.linearMap u).restrict fun _ hx ↦ (Finsupp.mem_submodule_iff _ _).mpr fun p ↦ by
    simpa using hu p (hx p)

@[simp]
theorem coe_map_apply (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) (x : Finsupp.submodule F)
    (p : ℤ) : (map u hu x : ℤ →₀ N) p = u ((x : ℤ →₀ M) p) := by
  simp [map]

@[simp]
theorem map_id : map (F := F) (G := F) LinearMap.id (fun _ ↦ le_rfl) = LinearMap.id := by
  ext x p
  simp

theorem map_comp (u : M →ₗ[R] N) (v : N →ₗ[R] P) (hu : ∀ p, F p ≤ (G p).comap u)
    (hv : ∀ p, G p ≤ (H p).comap v) :
    map (v ∘ₗ u) (fun p ↦ (hu p).trans (Submodule.comap_mono (hv p))) =
      map v hv ∘ₗ map u hu := by
  ext x p
  simp

/-- Rees maps commute with multiplication by the Rees parameter. -/
theorem map_comp_shift (hF : Monotone F) (hG : Monotone G) (u : M →ₗ[R] N)
    (hu : ∀ p, F p ≤ (G p).comap u) :
    map u hu ∘ₗ shift hF = shift hG ∘ₗ map u hu := by
  ext x p
  simp

/-- The Rees map sends the monomial `m z^p` to `u m z^p`. -/
@[simp]
theorem map_single (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) (p : ℤ) (m : F p) :
    map u hu (single F p m) = single G p ⟨u m, hu p m.property⟩ := by
  ext q
  simp [Finsupp.single_apply, apply_ite u]

/-- An element of `R_G N` lies in the image of the Rees map `R u` exactly when each of its
coefficients `n_p` is the image of an element of `F_p M`. -/
theorem mem_range_map_iff (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u)
    {y : Finsupp.submodule G} :
    y ∈ LinearMap.range (map u hu) ↔ ∀ p, (y : ℤ →₀ N) p ∈ (F p).map u := by
  classical
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, rfl⟩ p
    simpa using Submodule.mem_map_of_mem (f := u) (x.property p)
  · choose m hmF hmu using fun p ↦ (Submodule.mem_map.mp (hy p))
    -- Choose a preimage of each nonzero coefficient, and `0` for the zero coefficients.
    let x : ℤ →₀ M := Finsupp.onFinset (y : ℤ →₀ N).support
      (fun p ↦ if (y : ℤ →₀ N) p = 0 then 0 else m p) fun p hp ↦ by
        rw [Finsupp.mem_support_iff]
        intro h
        simp [h] at hp
    have hx : x ∈ Finsupp.submodule F := fun p ↦ by
      simp only [x, Finsupp.onFinset_apply]
      split_ifs
      exacts [zero_mem _, hmF p]
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [ext_iff]
    intro p
    simp only [coe_map_apply, x, Finsupp.onFinset_apply]
    split_ifs with h
    · simp [h]
    · exact hmu p

/-- A Rees monomial `n z^p` lies in the image of the Rees map `R u` exactly when `n` is the image
of an element of `F_p M`. -/
theorem single_mem_range_map_iff (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) {p : ℤ}
    {n : G p} : single G p n ∈ LinearMap.range (map u hu) ↔ (n : N) ∈ (F p).map u := by
  rw [mem_range_map_iff]
  refine ⟨fun h ↦ by simpa using h p, fun h q ↦ ?_⟩
  rcases eq_or_ne p q with rfl | hpq
  · simpa using h
  · simp [Finsupp.single_eq_of_ne' hpq]

/-- The image of a Rees map is stable under multiplication by the Rees parameter. -/
theorem range_map_le_comap_shift (hF : Monotone F) (hG : Monotone G) (u : M →ₗ[R] N)
    (hu : ∀ p, F p ≤ (G p).comap u) :
    LinearMap.range (map u hu) ≤ (LinearMap.range (map u hu)).comap (shift hG) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨shift hF x, LinearMap.congr_fun (map_comp_shift hF hG u hu) x⟩

/-- The Rees map vanishes exactly when `u` kills every coefficient. -/
theorem map_apply_eq_zero_iff (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u)
    (x : Finsupp.submodule F) : map u hu x = 0 ↔ ∀ p, u ((x : ℤ →₀ M) p) = 0 := by
  simp [ext_iff]

/-- A pair of filtered maps `f : (M, F) → (N, G)` and `g : (N, G) → (P, H)` is exact on every
filtration step exactly when the pair of Rees maps `R f`, `R g` is exact. -/
theorem exact_map_iff (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : ∀ p, F p ≤ (G p).comap f)
    (hg : ∀ p, G p ≤ (H p).comap g) :
    Function.Exact (map f hf) (map g hg) ↔
      ∀ p, Function.Exact (f.restrict fun _ hx ↦ hf p hx) (g.restrict fun _ hx ↦ hg p hx) := by
  -- Both sides are statements about coefficients: test the Rees side on monomials `n z^p`.
  have hstep (p : ℤ) (n : G p) :
      ((g.restrict fun _ hx ↦ hg p hx) n = 0 ↔ n ∈ Set.range (f.restrict fun _ hx ↦ hf p hx)) ↔
        (g n = 0 ↔ (n : N) ∈ (F p).map f) := by
    simp [← LinearMap.coe_range, LinearMap.range_restrict, ← Submodule.coe_eq_zero]
  refine ⟨fun h p n ↦ (hstep p n).mpr ?_, fun h y ↦ ?_⟩
  · have hy := h (single G p n)
    rwa [map_single, single_eq_zero, Submodule.mk_eq_zero, ← LinearMap.coe_range,
      SetLike.mem_coe, single_mem_range_map_iff] at hy
  · rw [map_apply_eq_zero_iff, ← LinearMap.coe_range, SetLike.mem_coe, mem_range_map_iff]
    exact forall_congr' fun p ↦ (hstep p ⟨_, y.property p⟩).mp (h p _)

end Map

/-! ### Specialization at `z = 1` -/

section EvalOne

variable (F) in
/-- Specialization of the Rees parameter at `z = 1`, sending `∑ m_p z^p` to `∑ m_p`. -/
noncomputable def evalOne : Finsupp.submodule F →ₗ[R] M :=
  Finsupp.lsum ℕ (fun _ : ℤ ↦ LinearMap.id) ∘ₗ (Finsupp.submodule F).subtype

theorem evalOne_apply (x : Finsupp.submodule F) :
    evalOne F x = (x : ℤ →₀ M).sum fun _ m ↦ m := by
  simp [evalOne, Finsupp.sum]

@[simp]
theorem evalOne_single (p : ℤ) (m : F p) : evalOne F (single F p m) = m := by
  simp [evalOne_apply]

/-- The image of the specialization at `z = 1` is the supremum `⨆_p F_p M` (the union when `F` is
increasing). -/
theorem range_evalOne : LinearMap.range (evalOne F) = ⨆ p, F p := by
  refine le_antisymm ?_ (iSup_le fun p m hm ↦ ⟨_, evalOne_single p ⟨m, hm⟩⟩)
  rintro _ ⟨x, rfl⟩
  rw [evalOne_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun p _ ↦ Submodule.mem_iSup_of_mem p (coe_apply_mem x p)

theorem evalOne_surjective (hex : ⨆ p, F p = ⊤) : Function.Surjective (evalOne F) := by
  rw [← LinearMap.range_eq_top, range_evalOne, hex]

/-- Specialization at `z = 1` is natural in the filtered map: `evalOne ∘ R u = u ∘ evalOne`. -/
@[simp]
theorem evalOne_map (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) (x : Finsupp.submodule F) :
    evalOne G (map u hu x) = u (evalOne F x) := by
  simp [evalOne_apply, map_finsuppSum, map, Finsupp.sum_mapRange_index]

@[simp]
theorem evalOne_shift (hF : Monotone F) (x : Finsupp.submodule F) :
    evalOne F (shift hF x) = evalOne F x := by
  rw [evalOne_apply, evalOne_apply, coe_shift, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.sum_equivMapDomain]

end EvalOne

end ReesModule

end Semiring

section Ring

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {F : ℤ → Submodule R M} {G : ℤ → Submodule R N}

namespace ReesModule

/-- A filtered map `u` is strict exactly when the Rees parameter `z` acts injectively on the
cokernel `R_G N / R u (R_F M)` of its Rees map, that is when this cokernel has no `z`-torsion.
The source filtration is assumed exhaustive. -/
theorem isStrict_iff_injective_mapQ_shift (hF : Monotone F) (hG : Monotone G)
    (hex : ⨆ p, F p = ⊤) (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) :
    u.IsStrict F G ↔ Function.Injective ((LinearMap.range (map u hu)).mapQ
      (LinearMap.range (map u hu)) (shift hG) (range_map_le_comap_shift hF hG u hu)) := by
  rw [LinearMap.isStrict_iff_forall_map_add_one_inf_le hF hG hu hex,
    ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  refine ⟨fun h c hc ↦ ?_, fun h p n ⟨hn₁, hn₂⟩ ↦ ?_⟩
  · -- `z y ∈ im R u` forces every coefficient `y_p ∈ G_p N` into `u (F_{p+1} M) ∩ G_p N`.
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_range_map_iff] at hc
    rw [Submodule.Quotient.mk_eq_zero, mem_range_map_iff]
    intro p
    exact h p ⟨by simpa using hc (p + 1), y.property p⟩
  · -- Test injectivity on the monomial `n z^p`, whose product with `z` is `R u (m z^{p+1})`.
    have hy := h (Submodule.Quotient.mk (single G p ⟨n, hn₂⟩)) <| by
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, shift_single,
        single_mem_range_map_iff]
      exact hn₁
    rwa [Submodule.Quotient.mk_eq_zero, single_mem_range_map_iff] at hy

/-! ### Specialization at `z = 1` -/

/-- The partial sum `∑_{q ≤ p} m_q`, with a minus sign: the element `y` with `(z - 1) y = x` for
an `x ∈ R_F M` whose coefficients sum to zero. -/
private noncomputable def partialSum (x : ℤ →₀ M) (p : ℤ) : M :=
  -∑ q ∈ x.support with q ≤ p, x q

private theorem partialSum_sub (x : ℤ →₀ M) (p : ℤ) :
    partialSum x (p - 1) - partialSum x p = x p := by
  classical
  have h (q : ℤ) : ((if q ≤ p then x q else 0) - if q ≤ p - 1 then x q else 0) =
      if p = q then x q else 0 := by
    split_ifs <;> first | omega | simp
  rw [partialSum, partialSum, neg_sub_neg, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_ite_eq]
  split_ifs with hp
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hp).symm

private theorem mem_biUnion_Ico_of_partialSum_ne_zero (x : ℤ →₀ M) (hx : (x.sum fun _ m ↦ m) = 0)
    {p : ℤ} (hp : partialSum x p ≠ 0) :
    p ∈ (x.support ×ˢ x.support).biUnion fun ab ↦ Finset.Ico ab.1 ab.2 := by
  classical
  simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_Ico, Prod.exists]
  -- The partial sum vanishes below the support, and above it equals the total sum.
  have hlow : ∃ a ∈ x.support, a ≤ p := by
    by_contra! h
    exact hp (by simp [partialSum, Finset.filter_false_of_mem fun q hq ↦ not_le.mpr (h q hq)])
  have hhigh : ∃ b ∈ x.support, p < b := by
    by_contra! h
    refine hp ?_
    rw [partialSum, Finset.filter_true_of_mem h, neg_eq_zero]
    exact hx
  obtain ⟨a, ha, hap⟩ := hlow
  obtain ⟨b, hb, hpb⟩ := hhigh
  exact ⟨a, b, ⟨ha, hb⟩, hap, hpb⟩

/-- The kernel of the specialization at `z = 1` is `(z - 1) R_F M`. -/
theorem ker_evalOne (hF : Monotone F) :
    LinearMap.ker (evalOne F) = LinearMap.range (shift hF - LinearMap.id) := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [LinearMap.mem_ker, evalOne_apply] at hx
    let y : ℤ →₀ M := Finsupp.onFinset _ (partialSum (x : ℤ →₀ M))
      fun p hp ↦ mem_biUnion_Ico_of_partialSum_ne_zero _ hx hp
    have hy : y ∈ Finsupp.submodule F := fun p ↦ by
      simp only [y, Finsupp.onFinset_apply, partialSum]
      refine neg_mem (Submodule.sum_mem _ fun q hq ↦ ?_)
      exact hF (Finset.mem_filter.mp hq).2 (x.property q)
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [ext_iff]
    intro p
    simp [y, partialSum_sub]
  · rintro _ ⟨y, rfl⟩
    simp

/-- Specialization at `z = 1`: for an exhaustive filtration, `R_F M / (z - 1) R_F M ≅ M`. -/
noncomputable def quotShiftSubIdEquiv (hF : Monotone F) (hex : ⨆ p, F p = ⊤) :
    (Finsupp.submodule F ⧸ LinearMap.range (shift hF - LinearMap.id)) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ (ker_evalOne hF).symm).trans
    ((evalOne F).quotKerEquivOfSurjective (evalOne_surjective hex))

@[simp]
theorem quotShiftSubIdEquiv_mk (hF : Monotone F) (hex : ⨆ p, F p = ⊤) (x : Finsupp.submodule F) :
    quotShiftSubIdEquiv hF hex (Submodule.Quotient.mk x) = evalOne F x := by
  rw [quotShiftSubIdEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-! ### Specialization at `z = 0` -/

section Symbol

/-- The underlying function of `TauCeti.ReesModule.symbol`. -/
private noncomputable def symbolFun (x : Finsupp.submodule F) : ⨁ p, GradedPiece F p :=
  DirectSum.mk (GradedPiece F) (x : ℤ →₀ M).support
    fun p ↦ Submodule.Quotient.mk ⟨(x : ℤ →₀ M) p, coe_apply_mem x p⟩

private theorem symbolFun_apply (x : Finsupp.submodule F) (p : ℤ) :
    symbolFun x p = Submodule.Quotient.mk ⟨(x : ℤ →₀ M) p, coe_apply_mem x p⟩ := by
  by_cases hx : p ∈ (x : ℤ →₀ M).support
  · exact DirectSum.mk_apply_of_mem hx
  · rw [symbolFun, DirectSum.mk_apply_of_notMem (by simpa using hx), eq_comm,
      Submodule.Quotient.mk_eq_zero]
    simp [Finsupp.notMem_support_iff.mp hx]

variable (F) in
/-- Specialization of the Rees parameter at `z = 0`: the map `R_F M → gr^F M` sending
`∑ m_p z^p` to the family of classes of `m_p` in `F_p M / F_{p-1} M`. -/
noncomputable def symbol : Finsupp.submodule F →ₗ[R] ⨁ p, GradedPiece F p where
  toFun := symbolFun
  map_add' x y := by
    ext p
    simp [symbolFun_apply, ← Submodule.Quotient.mk_add]
  map_smul' c x := by
    ext p
    simp [DirectSum.smul_apply, symbolFun_apply, ← Submodule.Quotient.mk_smul]

@[simp]
theorem symbol_apply (x : Finsupp.submodule F) (p : ℤ) :
    symbol F x p = Submodule.Quotient.mk ⟨(x : ℤ →₀ M) p, coe_apply_mem x p⟩ :=
  symbolFun_apply x p

/-- The kernel of the specialization at `z = 0` is `z R_F M`. -/
theorem ker_symbol (hF : Monotone F) :
    LinearMap.ker (symbol F) = LinearMap.range (shift hF) := by
  ext x
  rw [LinearMap.mem_ker, mem_range_shift_iff, DFinsupp.ext_iff]
  simp

@[simp]
theorem symbol_single (p : ℤ) (m : F p) :
    symbol F (single F p m) = DirectSum.of (GradedPiece F) p (Submodule.Quotient.mk m) := by
  classical
  ext q
  rw [symbol_apply]
  rcases eq_or_ne p q with rfl | hpq
  · simp
  · rw [DirectSum.of_eq_of_ne (β := GradedPiece F) _ _ _ hpq.symm, Submodule.Quotient.mk_eq_zero]
    simp [Finsupp.single_eq_of_ne' hpq]

theorem symbol_surjective : Function.Surjective (symbol F) := by
  classical
  intro c
  induction c using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of p a =>
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    exact ⟨single F p m, symbol_single p m⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩

/-- The map `R_F M / z R_F M → gr^F M` induced by `TauCeti.ReesModule.symbol`. -/
private noncomputable def symbolQuot (hF : Monotone F) :
    (Finsupp.submodule F ⧸ LinearMap.range (shift hF)) →ₗ[R] ⨁ p, GradedPiece F p :=
  -- Built with `liftQ`: `quotKerEquivOfSurjective` would compare the two instance paths on
  -- `⨁ p, GradedPiece F p` inside `LinearMap.ker (symbol F)`, which elaborates very slowly.
  Submodule.liftQ (M₂ := ⨁ p, GradedPiece F p) _ (symbol F) (ker_symbol hF).ge

private theorem symbolQuot_mk (hF : Monotone F) (x : Finsupp.submodule F) :
    symbolQuot hF (Submodule.Quotient.mk x) = symbol F x :=
  Submodule.liftQ_apply _ _ _

/-- Specialization at `z = 0`: `R_F M / z R_F M ≅ gr^F M = ⊕_p F_p M / F_{p-1} M`. -/
noncomputable def quotShiftEquiv (hF : Monotone F) :
    (Finsupp.submodule F ⧸ LinearMap.range (shift hF)) ≃ₗ[R] ⨁ p, GradedPiece F p :=
  LinearEquiv.ofBijective (symbolQuot hF) (show Function.Bijective (symbolQuot hF) from
    ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (ker_symbol hF).symm),
      -- `Submodule.range_liftQ` is stated with the `AddCommGroup` instance path on
      -- `⨁ p, GradedPiece F p`, and unifying it with the `AddCommMonoid` one times out.
      fun c ↦ let ⟨x, hx⟩ := symbol_surjective c
        ⟨Submodule.Quotient.mk x, (symbolQuot_mk hF x).trans hx⟩⟩)

@[simp]
theorem quotShiftEquiv_mk (hF : Monotone F) (x : Finsupp.submodule F) :
    quotShiftEquiv hF (Submodule.Quotient.mk x) = symbol F x := by
  rw [quotShiftEquiv, LinearEquiv.ofBijective_apply, symbolQuot_mk]

end Symbol

end ReesModule

end Ring

end TauCeti
