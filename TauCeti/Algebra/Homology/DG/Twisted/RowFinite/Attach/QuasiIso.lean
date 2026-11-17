/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Basic
import TauCeti.Data.Finsupp.Sum

/-!
# Extending quasi-isomorphisms over attached free generators

Let `m` be a row-finite twisting cocycle on `(P, ind)`, with free differential graded left module
`K_m = P →₀ A`, and let `M` be a differential graded left module with two `A`-submodules
`N₀ ≤ N₁`. A map `g : K_m → M`, given on generators and landing in `N₀`, compares `K_m` with
`N₀`. We say that its relative cycles are relative boundaries when every pair `(u, w)` with
`D u = 0`, `w ∈ N₀` and `g u = d w` is of the form `(D u', g u' + d w')` with `w' ∈ N₀`. When
`g` commutes with the differentials and `N₀` is closed under `d`, this is the acyclicity of the
mapping cone of `g : K_m → N₀`, written on elements, so it says that `g` is a quasi-isomorphism
onto `N₀` (compare `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`).

Attaching free generators `Q` along cycles `a q` of `K_m`
(`TauCeti.RowFiniteTwistingCocycle.attach`) and sending the generator `e_q` to an element `c q`
with `d (c q) = g (a q)` extends `g` to `Sum.elim g c : K_{attach} → M`. This file proves that
the extension is again a quasi-isomorphism, now onto `N₁`, as soon as the elements `c q` lie in
`N₁` (so that the extension lands in `N₁`) and the new generators are quasi-isomorphic to the
quotient `N₁ / N₀`: every `y : Q →₀ A` with `d y = 0` and every `w ∈ N₁`
with `c(y) - d w ∈ N₀` admit `y'` and `w' ∈ N₁` with `d y' = y` and `c(y') + d w' - w ∈ N₀`
(`TauCeti.RowFiniteTwistingCocycle.exists_attach_differential_eq_of_forall_exists`, whose
conclusion on relative cycles holds without the membership `c q ∈ N₁`). The proof
is the five lemma for the short exact sequences `0 → K_m → K_{attach} → K_0(Q) → 0` and
`0 → N₀ → N₁ → N₁ / N₀ → 0`, written as a chase on elements so that no quotient complex is formed.

The attaching data are found from the relative cycles of `N₁` modulo `N₀`
(`TauCeti.RowFiniteTwistingCocycle.exists_linearCombination_eq_differential_add`): if
`d z ∈ N₀`, then `d z` is a cycle of `N₀`, so it is the image of a cycle `u` of `K_m` up to a
boundary `d k` with `k ∈ N₀`. The cycle `u` is the attaching cycle and `z + k` the corrected image
of the new generator, of the same degree as `z` when `N₀` is a homogeneous submodule. Putting the
two steps together (`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`), relative
cycles `c₀ q` of `N₁` representing generators of `N₁ / N₀` give a cell attachment together with
a map landing in `N₁` that is a quasi-isomorphism onto `N₁`, of the same shape as the one onto
`N₀` that it started from, so the step can be iterated along a filtration.

This is the inductive step in the construction of semi-free resolutions one cell at a time, as in
Brown's twisted tensor products: for the chains on the based path space of a CW complex, filtered
by the preimages of the skeleta, the relative chains over the `n`-cells are quasi-isomorphic to a
free module over the chains on the loop space with one generator per cell, and attaching these
generators one skeleton at a time builds a semi-free model of the chains on the path space.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.exists_attach_differential_eq_of_forall_exists`: attaching
  generators that are quasi-isomorphic to `N₁ / N₀` extends a quasi-isomorphism onto `N₀` to one
  onto `N₁`.
* `TauCeti.RowFiniteTwistingCocycle.exists_linearCombination_eq_differential_add`: a relative
  cycle of `N₁` modulo `N₀` is corrected, within its degree, to bound the image of a cycle of
  `K_m`.
* `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`: the two steps together.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6 (semifree modules).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uM uP uQ

variable {R : Type uR} {A : Type uA} {P : Type uP} {Q : Type uQ}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ} {indQ : Q → ℤ}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 d P ind) (hM : IsDGLeftModule h ℳ dM)
  {N₀ N₁ : Submodule A M} {g : P → M}

include hM

variable {a : Q → P →₀ A} (ha : ∀ q y, a q y ∈ 𝒜 (ind y - indQ q + 1))
  (hca : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (a q) = 0)

/-- **Attaching generators quasi-isomorphic to the relative part extends a quasi-isomorphism.**
Let `g : K_m → M` land in `N₀ ≤ N₁` and have relative cycles, with target in `N₀`, that are
relative boundaries. Extend it to the attached module by sending each new generator `e_q` to an
element `c q` bounding the image of its attaching cycle. If the new generators are
quasi-isomorphic, through `c`, to `N₁` modulo `N₀`, then every relative cycle of the extension
with target in `N₁` is a relative boundary with target in `N₁`. This conclusion does not need the
new images `c q` to lie in `N₁`; when they do, the extension lands in `N₁` and the conclusion says
that it is a quasi-isomorphism onto `N₁`. -/
theorem exists_attach_differential_eq_of_forall_exists (hN : N₀ ≤ N₁) (hgN : ∀ x, g x ∈ N₀)
    (hg : ∀ x, linearCombination A g (m.m x) = dM (g x)) {c : Q → M}
    (hc : ∀ q, linearCombination A g (a q) = dM (c q))
    (hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = 0 →
      linearCombination A g u = dM w → w ∈ N₀ → ∃ (u' : P →₀ A) (w' : M), w' ∈ N₀ ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u' = u ∧
          linearCombination A g u' + dM w' = w)
    (hQ : ∀ (y : Q →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N₁ →
      linearCombination A c y - dM w ∈ N₀ → ∃ (y' : Q →₀ A) (w' : M), w' ∈ N₁ ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c y' + dM w' - w ∈ N₀)
    {f : P ⊕ Q →₀ A} {w : M}
    (hf : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m f = 0)
    (hfw : linearCombination A (Sum.elim g c) f = dM w) (hw : w ∈ N₁) :
    ∃ (f' : P ⊕ Q →₀ A) (w' : M), w' ∈ N₁ ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m f' = f ∧
        linearCombination A (Sum.elim g c) f' + dM w' = w := by
  classical
  -- The extension commutes with the differentials, and splits along the two kinds of generators.
  have hΦ := (m.forall_linearCombination_attach_differential_iff ha hca hM g c).2
    ⟨linearCombination_rowFiniteTwistedDifferential hM m.m hg, hc⟩
  have hΦ' (u : P →₀ A) (y : Q →₀ A) : linearCombination A (Sum.elim g c) (sumElim u y) =
      linearCombination A g u + linearCombination A c y := by
    simp only [sumElim_eq_add, map_add, linearCombination_mapDomain, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
  -- Split `f` into its coordinates `u` on the old generators and `y` on the new ones.
  obtain ⟨u, y, rfl⟩ : ∃ u y, f = sumElim u y :=
    ⟨(sumFinsuppEquivProdFinsupp f).1, (sumFinsuppEquivProdFinsupp f).2, by ext (x | q) <;> simp⟩
  rw [attach_differential_sumElim, ← sumElim_zero_zero, sumElim_inj] at hf
  obtain ⟨hu, hy⟩ := hf
  rw [hΦ'] at hfw
  -- The new coordinates are a relative cycle modulo `N₀`, hence a relative boundary.
  obtain ⟨y', w₁, hw₁, hy', hyw⟩ := hQ y w hy hw <| by
    rw [show linearCombination A c y - dM w = -linearCombination A g u by rw [← hfw]; abel]
    refine N₀.neg_mem (Submodule.span_le.2 (Set.range_subset_iff.2 hgN) ?_)
    exact mem_span_range_iff_exists_finsupp.2 ⟨u, by rw [linearCombination_apply]⟩
  -- The differential of the lift `y'` of the new coordinates, read off from `D² = 0`.
  have hDS : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m
      (rowFiniteSignedMap (𝒜 := 𝒜) a y') + rowFiniteSignedMap (𝒜 := 𝒜) a y = 0 := by
    have h₀ := (m.attach a ha hca).differential_sq_zero h (sumElim 0 y')
    rw [attach_differential_sumElim, map_zero, zero_add, hy', attach_differential_sumElim,
      ← sumElim_zero_zero, sumElim_inj] at h₀
    exact h₀.1
  have hΦS : linearCombination A g (rowFiniteSignedMap (𝒜 := 𝒜) a y') +
      linearCombination A c y = dM (linearCombination A c y') := by
    have h₀ := hΦ (sumElim 0 y')
    rwa [attach_differential_sumElim, map_zero, zero_add, hy', hΦ', hΦ', map_zero, zero_add] at h₀
  -- What is left is a relative cycle of `g` with target in `N₀`, hence a relative boundary.
  obtain ⟨u', w', hw', hu', huw⟩ := hK (u - rowFiniteSignedMap (𝒜 := 𝒜) a y')
    (w - linearCombination A c y' - dM w₁)
    (by rw [map_sub, eq_neg_of_add_eq_zero_left hu, eq_neg_of_add_eq_zero_left hDS, sub_self])
    (by
      simp only [map_sub, hM.sq_zero, sub_zero]
      rw [← hfw, ← hΦS]
      abel)
    (by
      rw [show w - linearCombination A c y' - dM w₁ =
        -(linearCombination A c y' + dM w₁ - w) by abel]
      exact N₀.neg_mem hyw)
  refine ⟨sumElim u' y', w₁ + w', N₁.add_mem hw₁ (hN hw'), ?_, ?_⟩
  · rw [attach_differential_sumElim, hu', hy', sub_add_cancel]
  · rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq] at huw
    rw [hΦ', map_add, ← huw]
    abel

variable {m} in
/-- **Correcting a relative cycle to bound the image of a cycle.** Let `g : K_m → M`, sending
each generator `x` to degree `-ind x`, have relative cycles with target in the homogeneous
submodule `N₀` that are relative boundaries. If `z` has degree `n` and `d z ∈ N₀`, then some
`k ∈ N₀` of degree `n` and some cycle `u` of `K_m` of degree `n + 1` satisfy `g u = d (z + k)`. -/
theorem exists_linearCombination_eq_differential_add (hN₀ : N₀.IsHomogeneous ℳ)
    (hg : ∀ x, g x ∈ ℳ (-ind x))
    (hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = 0 →
      linearCombination A g u = dM w → w ∈ N₀ → ∃ (u' : P →₀ A) (w' : M), w' ∈ N₀ ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u' = u ∧
          linearCombination A g u' + dM w' = w)
    {n : ℤ} {z : M} (hz : z ∈ ℳ n) (hdz : dM z ∈ N₀) :
    ∃ (u : P →₀ A) (k : M), u ∈ rowFiniteTotalGrading 𝒜 ind (n + 1) ∧ k ∈ N₀ ∧ k ∈ ℳ n ∧
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = 0 ∧
        linearCombination A g u = dM (z + k) := by
  classical
  -- The cycle `d z` of `N₀` is the image of a cycle of `K_m` up to a boundary.
  obtain ⟨u, k, hk, hu, huk⟩ := hK 0 (dM z) (map_zero _) (by rw [map_zero, hM.sq_zero]) hdz
  -- Keep the components in the right degrees.
  refine ⟨(DirectSum.decompose (rowFiniteTotalGrading 𝒜 ind) u (n + 1) : P →₀ A),
    -(DirectSum.decompose ℳ k n : M), SetLike.coe_mem _,
    N₀.neg_mem ((Submodule.IsHomogeneous.mem_iff ℳ hN₀).1 hk n), neg_mem (SetLike.coe_mem _),
    ?_, ?_⟩
  · rw [(m.isDGLeftModule_rowFiniteTwistedDifferential h).map_decompose, hu,
      DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  · have hdeg := DirectSum.map_decompose_shift (rowFiniteTotalGrading 𝒜 ind) ℳ
      (linearCombination A g).toAddMonoidHom id Function.injective_id
      (fun _ _ hx ↦ linearCombination_mem_of_mem_rowFiniteTotalGrading hg hx) (n + 1) u
    simp only [LinearMap.toAddMonoidHom_coe, id_eq] at hdeg
    rw [hdeg, eq_sub_of_add_eq huk, ← sub_eq_add_neg, ← map_sub, ← hM.map_decompose,
      DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      DirectSum.decompose_of_mem_same ℳ hz]

/-- **One cell attachment of a semi-free model.** Let `g : K_m → M`, sending each generator `x`
into `N₀` in degree `-ind x`, commute with the differentials and have relative cycles, with
target in the homogeneous submodule `N₀`, that are relative boundaries. Let `c₀ q`, of degree
`-indQ q`, be relative cycles of `N₁` modulo `N₀ ≤ N₁` through which the free module on `Q`, with
its coefficient differential, is quasi-isomorphic to `N₁` modulo `N₀`. Then there are attaching
cycles `a q` of `K_m` and corrections `c q ≡ c₀ q` modulo `N₀`, of the same degrees and in `N₁`,
with `d (c q) = g (a q)`, such that `Sum.elim g c` on the attached module, which lands in `N₁`, has
relative cycles, with target in `N₁`, that are relative boundaries. -/
theorem exists_attach_of_forall_exists (hN₀ : N₀.IsHomogeneous ℳ) (hN : N₀ ≤ N₁)
    (hgN : ∀ x, g x ∈ N₀) (hgdeg : ∀ x, g x ∈ ℳ (-ind x))
    (hg : ∀ x, linearCombination A g (m.m x) = dM (g x))
    (hK : ∀ (u : P →₀ A) (w : M), rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = 0 →
      linearCombination A g u = dM w → w ∈ N₀ → ∃ (u' : P →₀ A) (w' : M), w' ∈ N₀ ∧
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u' = u ∧
          linearCombination A g u' + dM w' = w)
    {c₀ : Q → M} (hc₀ : ∀ q, c₀ q ∈ ℳ (-indQ q)) (hc₀N : ∀ q, c₀ q ∈ N₁)
    (hdc₀ : ∀ q, dM (c₀ q) ∈ N₀)
    (hQ : ∀ (y : Q →₀ A) (w : M), mapRange.linearMap d y = 0 → w ∈ N₁ →
      linearCombination A c₀ y - dM w ∈ N₀ → ∃ (y' : Q →₀ A) (w' : M), w' ∈ N₁ ∧
        mapRange.linearMap d y' = y ∧ linearCombination A c₀ y' + dM w' - w ∈ N₀) :
    ∃ (a : Q → P →₀ A) (ha : ∀ q y, a q y ∈ 𝒜 (ind y - indQ q + 1))
      (hca : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (a q) = 0) (c : Q → M),
      (∀ q, c q ∈ ℳ (-indQ q)) ∧ (∀ q, c q ∈ N₁) ∧ (∀ q, c q - c₀ q ∈ N₀) ∧
      (∀ q, linearCombination A g (a q) = dM (c q)) ∧
      ∀ (f : P ⊕ Q →₀ A) (w : M),
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m f = 0 →
        linearCombination A (Sum.elim g c) f = dM w → w ∈ N₁ → ∃ (f' : P ⊕ Q →₀ A) (w' : M),
          w' ∈ N₁ ∧ rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m f' = f ∧
            linearCombination A (Sum.elim g c) f' + dM w' = w := by
  choose a k ha hk hkdeg hca hak using fun q ↦
    exists_linearCombination_eq_differential_add hM hN₀ hgdeg hK (hc₀ q) (hdc₀ q)
  have ha' (q : Q) (y : P) : a q y ∈ 𝒜 (ind y - indQ q + 1) := by
    convert (mem_rowFiniteTotalGrading_iff 𝒜 ind).1 (ha q) y using 2
    ring
  -- The corrections differ from `c₀` by elements of `N₀`, so `hQ` transfers to them.
  have hdiff (y : Q →₀ A) : linearCombination A (fun q ↦ c₀ q + k q) y -
      linearCombination A c₀ y ∈ N₀ := by
    rw [show linearCombination A (fun q ↦ c₀ q + k q) y =
        linearCombination A c₀ y + linearCombination A k y by
      simp only [linearCombination_apply, smul_add, Finsupp.sum_add], add_sub_cancel_left]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 hk)
      (mem_span_range_iff_exists_finsupp.2 ⟨y, by rw [linearCombination_apply]⟩)
  refine ⟨a, ha', hca, fun q ↦ c₀ q + k q, fun q ↦ add_mem (hc₀ q) (hkdeg q),
    fun q ↦ N₁.add_mem (hc₀N q) (hN (hk q)), fun q ↦ by simpa using hk q, hak,
    fun f w hf hfw hw ↦ ?_⟩
  refine m.exists_attach_differential_eq_of_forall_exists hM ha' hca hN hgN hg hak hK
    (fun y w hy hw hyw ↦ ?_) hf hfw hw
  obtain ⟨y', w', hw', hy', hyw'⟩ := hQ y w hy hw <| by
    rw [show linearCombination A c₀ y - dM w = linearCombination A (fun q ↦ c₀ q + k q) y -
      dM w - (linearCombination A (fun q ↦ c₀ q + k q) y - linearCombination A c₀ y) by abel]
    exact N₀.sub_mem hyw (hdiff y)
  refine ⟨y', w', hw', hy', ?_⟩
  rw [show linearCombination A (fun q ↦ c₀ q + k q) y' + dM w' - w =
    linearCombination A c₀ y' + dM w' - w +
      (linearCombination A (fun q ↦ c₀ q + k q) y' - linearCombination A c₀ y') by abel]
  exact N₀.add_mem hyw' (hdiff y')

end RowFiniteTwistingCocycle

end TauCeti
