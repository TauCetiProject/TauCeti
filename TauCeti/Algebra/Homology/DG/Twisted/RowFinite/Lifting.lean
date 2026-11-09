/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence

/-!
# The lifting property of semi-free row-finite twisted modules

Let `m` be a row-finite twisting cocycle on a graded basis `(P, ind)` which is one-sided,
`m x y = 0` whenever `ind x ≤ ind y`, and whose generator indices are bounded below. Its free
differential graded left module `K_m = P →₀ A` is then **semi-free**: it is built by attaching
the generators in order of increasing index, each along a cycle in the span of the earlier ones.
This file proves the lifting property which makes semi-free modules the cofibrant objects of
differential graded left modules.

Let `f : N → N'` be a degree-zero map of differential graded left modules which is a
quasi-isomorphism, in the elementwise form that every relative cycle `(c, w)`, with `d c = 0`
and `f c = d w`, is a relative boundary `(d u, f u + d v)`. This is the acyclicity of the mapping
cone of `f`, the form used by `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists` on the right.

* **Existence of lifts** (`TauCeti.RowFiniteTwistingCocycle.exists_lift`). Every chain map
  `g : K_m → N'` lifts along `f` up to homotopy: there are a chain map `g' : K_m → N` and a
  homotopy from `f ∘ g'` to `g`.
* **Uniqueness of lifts** (`TauCeti.RowFiniteTwistingCocycle.exists_homotopy_of_homotopy_comp`).
  Two chain maps `g₀ g₁ : K_m → N` with `f ∘ g₀` homotopic to `f ∘ g₁` are homotopic.

Chain maps out of `K_m` are given by the images of the generators, through
`Finsupp.linearCombination`, and homotopies by the images of the generators, through the signed
extension `TauCeti.rowFiniteSignedMap`. Both constructions choose the images of the generators by
well-founded recursion on the index. At a generator `x` the earlier choices already make the
image of its row `m x` into a relative cycle of `f`, and a relative boundary of `f` bounding it
gives the next choice.

Applied to two semi-free resolutions `ε : K_{mP} → N` and `ε' : K_{mQ} → N` of the same module,
the two properties give continuation cocycles in both directions, with homotopies joining both
composites to the identity: the cocycles are homologous
(`TauCeti.nonempty_rowFiniteHomologous`). So for every DG right
module `M` the twisted complexes `M ⊗_A K_{mP}` and `M ⊗_A K_{mQ}` are homotopy equivalent
(`TauCeti.RowFiniteHomologous.homotopyEquiv`), which is the independence of the derived tensor
product `M ⊗^L_A N` from the semi-free resolution used to compute it. In particular a continuation
cocycle which is a quasi-isomorphism is itself a homotopy equivalence
(`TauCeti.RowFiniteContinuationCocycle.exists_rowFiniteHomologous_ν_eq`).

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6 (semifree modules), Proposition 6.4.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open DirectSum

namespace TauCeti

universe uR uA uN uN' uP uX

/-- **Choices by well-founded recursion.** Let `V F x v` say that `v` is an admissible value at
`x` for a function `F`, depending only on the values of `F` at points below `x`. If an admissible
value exists at `x` as soon as `F` takes admissible values at all points below `x`, then some
function takes admissible values everywhere. -/
private theorem exists_forall_of_wellFounded {α : Type uP} {X : Type uX} [Nonempty X]
    {r : α → α → Prop} (hr : WellFounded r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (V : (α → X) → α → X → Prop)
    (hV : ∀ ⦃x v⦄ ⦃F F' : α → X⦄, (∀ y, r y x → F y = F' y) → V F x v → V F' x v)
    (hex : ∀ x (F : α → X), (∀ y, r y x → V F y (F y)) → ∃ v, V F x v) :
    ∃ G : α → X, ∀ x, V G x (G x) := by
  classical
  let F (x : α) (IH : ∀ y, r y x → X) : α → X := fun y ↦
    if hy : r y x then IH y hy else Classical.arbitrary X
  let step (x : α) (IH : ∀ y, r y x → X) : X :=
    if hc : ∀ y, r y x → V (F x IH) y (F x IH y) then (hex x _ hc).choose
    else Classical.arbitrary X
  refine ⟨hr.fix step, fun x ↦
    hr.induction (C := fun x ↦ V (hr.fix step) x (hr.fix step x)) x fun x ih ↦ ?_⟩
  have hF : ∀ y, r y x → F x (fun y _ ↦ hr.fix step y) y = hr.fix step y :=
    fun y hy ↦ dite_eq_left hy
  have hc : ∀ y, r y x →
      V (F x fun y _ ↦ hr.fix step y) y (F x (fun y _ ↦ hr.fix step y) y) := fun y hy ↦ by
    rw [hF y hy]
    exact hV (fun z hz ↦ (hF z (htrans hz hy)).symm) (ih y hy)
  have hGx : hr.fix step x = (hex x _ hc).choose := by
    rw [hr.fix_eq step x]
    exact dite_eq_left hc
  rw [hGx]
  exact hV hF (hex x _ hc).choose_spec

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {dN : N →ₗ[R] N}
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {𝒩' : ℤ → Submodule R N'} [SetLike.GradedSMul 𝒜 𝒩'] [DirectSum.Decomposition 𝒩']
  {dN' : N' →ₗ[R] N'}

/-- A homogeneous relative cycle of a degree-zero map whose relative cycles are relative
boundaries is the relative boundary of homogeneous elements of the matching degrees. -/
private theorem exists_mem_of_forall_exists (hN : IsDGLeftModule hA 𝒩 dN)
    (hN' : IsDGLeftModule hA 𝒩' dN') {f : N →ₗ[A] N'} (hf : LinearMap.IsHomogeneous f 𝒩 𝒩' 0)
    (hrel : ∀ c w, dN c = 0 → f c = dN' w → ∃ u v, dN u = c ∧ f u + dN' v = w)
    {n : ℤ} {c : N} {w : N'} (hc : c ∈ 𝒩 n) (hw : w ∈ 𝒩' (n - 1)) (hdc : dN c = 0)
    (hcw : f c = dN' w) :
    ∃ u v, u ∈ 𝒩 (n - 1) ∧ v ∈ 𝒩' (n - 1 - 1) ∧ dN u = c ∧ f u + dN' v = w := by
  obtain ⟨u, v, hu, huv⟩ := hrel c w hdc hcw
  refine ⟨decompose 𝒩 u (n - 1), decompose 𝒩' v (n - 1 - 1), SetLike.coe_mem _,
    SetLike.coe_mem _, ?_, ?_⟩
  · rw [hN.map_decompose, sub_add_cancel, hu, decompose_of_mem_same _ hc]
  · rw [hf.map_decompose, hN'.map_decompose, add_zero, sub_add_cancel,
      ← Submodule.coe_add, ← DirectSum.add_apply, ← decompose_add, huv,
      decompose_of_mem_same _ hw]

namespace RowFiniteTwistingCocycle

variable {P : Type uP} {ind : P → ℤ}

omit [GradedAlgebra 𝒜] in
/-- In a one-sided cocycle whose indices are bounded below by `p₀`, the generators in the row of
`x` have strictly smaller index, measured from `p₀`. -/
private theorem toNat_lt_toNat_of_mem_support (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) {x y : P}
    (hy : y ∈ (m.m x).support) : (ind y - p₀).toNat < (ind x - p₀).toNat := by
  have hlt : ind y < ind x := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hy (hm x y (not_lt.mp h))
  have := hp₀ y
  omega

omit [GradedAlgebra 𝒜] in
/-- The row of a generator `x` has total degree `1 - ind x`. -/
private theorem m_mem_rowFiniteTotalGrading (m : RowFiniteTwistingCocycle 𝒜 d P ind) (x : P) :
    m.m x ∈ rowFiniteTotalGrading 𝒜 ind (1 - ind x) := by
  refine (mem_rowFiniteTotalGrading_iff _ _).mpr fun y ↦ ?_
  rw [show 1 - ind x + ind y = ind y - ind x + 1 by ring]
  exact m.mem_graded x y

/-- **Lifting along a quasi-isomorphism.** Let `m` be one-sided with generator indices bounded
below, so that `K_m` is semi-free, and let `f : N → N'` be a degree-zero map of DG left modules
whose relative cycles are relative boundaries. Every chain map `K_m → N'`, given by the images
`g x` of the generators, lifts along `f` up to homotopy: there are images `g' x` of the
generators in `N`, defining a chain map `K_m → N`, and a homotopy `k`, with
`d (k x) + k (m x) = g x - f (g' x)` on every generator. -/
theorem exists_lift (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN')
    {f : N →ₗ[A] N'} (hf : LinearMap.IsHomogeneous f 𝒩 𝒩' 0)
    (hrel : ∀ c w, dN c = 0 → f c = dN' w → ∃ u v, dN u = c ∧ f u + dN' v = w)
    {g : P → N'} (hg : ∀ x, g x ∈ 𝒩' (-ind x))
    (hgd : ∀ x, Finsupp.linearCombination A g (m.m x) = dN' (g x)) :
    ∃ (g' : P → N) (k : P → N'), (∀ x, g' x ∈ 𝒩 (-ind x)) ∧ (∀ x, k x ∈ 𝒩' (-ind x - 1)) ∧
      (∀ x, Finsupp.linearCombination A g' (m.m x) = dN (g' x)) ∧
      ∀ x, dN' (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x) = g x - f (g' x) := by
  classical
  let μ : P → ℕ := fun x ↦ (ind x - p₀).toNat
  have hsupp : ∀ x, ∀ y ∈ (m.m x).support, μ y < μ x := fun x y hy ↦
    m.toNat_lt_toNat_of_mem_support hm hp₀ hy
  -- An admissible pair of images at `x`, given the earlier images.
  let V : (P → N × N') → P → N × N' → Prop := fun F x v ↦
    v.1 ∈ 𝒩 (-ind x) ∧ v.2 ∈ 𝒩' (-ind x - 1) ∧
      Finsupp.linearCombination A (Prod.fst ∘ F) (m.m x) = dN v.1 ∧
      dN' v.2 + rowFiniteSignedMap (𝒜 := 𝒜) (Prod.snd ∘ F) (m.m x) = g x - f v.1
  suffices hGex : ∃ G : P → N × N', ∀ x, V G x (G x) by
    obtain ⟨G, hG⟩ := hGex
    exact ⟨Prod.fst ∘ G, Prod.snd ∘ G, fun x ↦ (hG x).1, fun x ↦ (hG x).2.1,
      fun x ↦ (hG x).2.2.1, fun x ↦ (hG x).2.2.2⟩
  refine exists_forall_of_wellFounded (r := fun y x ↦ μ y < μ x) (measure μ).wf
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) V ?_ ?_
  · -- Admissibility only depends on the images of the generators in the row.
    rintro x v F F' hFF' ⟨h₁, h₂, h₃, h₄⟩
    have hc : ∀ y ∈ (m.m x).support, F y = F' y := fun y hy ↦ hFF' y (hsupp x y hy)
    refine ⟨h₁, h₂, ?_, ?_⟩
    · rw [← h₃, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      exact Finsupp.sum_congr fun y hy ↦ by simp [hc y hy]
    · rw [← h₄, rowFiniteSignedMap_congr (h' := Prod.snd ∘ F) fun y hy ↦ by simp [hc y hy]]
  · -- The image of the row is a relative cycle, and a bounding relative boundary is admissible.
    intro x F hF
    have hval : ∀ y ∈ (m.m x).support, V F y (F y) := fun y hy ↦ hF y (hsupp x y hy)
    have hrow := m.m_mem_rowFiniteTotalGrading x
    have hc : Finsupp.linearCombination A (Prod.fst ∘ F) (m.m x) ∈ 𝒩 (1 - ind x) := by
      simpa using linearCombination_mem_of_mem_support (j := 0) hrow fun y hy ↦ by
        simpa using (hval y hy).1
    have hw : g x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.snd ∘ F) (m.m x) ∈ 𝒩' (1 - ind x - 1) := by
      refine sub_mem (by simpa using hg x) ?_
      simpa [sub_eq_add_neg] using rowFiniteSignedMap_mem_of_mem_support (j := -1) hrow
        fun y hy ↦ by simpa [sub_eq_add_neg] using (hval y hy).2.1
    have hdc : dN (Finsupp.linearCombination A (Prod.fst ∘ F) (m.m x)) = 0 := by
      rw [← linearCombination_rowFiniteTwistedDifferential_of_mem_support hN m.m
        fun y hy ↦ (hval y hy).2.2.1, m.differential_row x, map_zero]
    have hcw : f (Finsupp.linearCombination A (Prod.fst ∘ F) (m.m x)) =
        dN' (g x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.snd ∘ F) (m.m x)) := by
      have key := rowFiniteSignedMap_differential_of_mem_support hN' m.m
        (Φ := Finsupp.linearCombination A g - f ∘ₗ Finsupp.linearCombination A (Prod.fst ∘ F))
        (k := Prod.snd ∘ F) fun y hy ↦ by
          rw [LinearMap.sub_apply, LinearMap.comp_apply, Finsupp.linearCombination_single,
            Finsupp.linearCombination_single, one_smul, one_smul]
          exact (hval y hy).2.2.2
      rw [m.differential_row x, map_zero, add_zero, LinearMap.sub_apply,
        LinearMap.comp_apply] at key
      rw [map_sub, ← hgd x, key, sub_sub_cancel]
    obtain ⟨u, v, hu, hv, hdu, huv⟩ := exists_mem_of_forall_exists hN hN' hf hrel hc hw hdc hcw
    refine ⟨(u, v), by simpa using hu, by simpa [sub_sub] using hv, hdu.symm, ?_⟩
    rw [eq_sub_iff_add_eq] at huv ⊢
    rw [← huv]
    abel

/-- **Uniqueness of lifts up to homotopy.** Let `m` be one-sided with generator indices bounded
below, so that `K_m` is semi-free, and let `f : N → N'` be a degree-zero map of DG left modules
whose relative cycles are relative boundaries. If two chain maps `g₀ g₁ : K_m → N` become
homotopic after composing with `f`, through a homotopy `k` with
`d (k x) + k (m x) = f (g₁ x) - f (g₀ x)`, then they are homotopic. -/
theorem exists_homotopy_of_homotopy_comp (m : RowFiniteTwistingCocycle 𝒜 d P ind)
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN')
    {f : N →ₗ[A] N'} (hf : LinearMap.IsHomogeneous f 𝒩 𝒩' 0)
    (hrel : ∀ c w, dN c = 0 → f c = dN' w → ∃ u v, dN u = c ∧ f u + dN' v = w)
    {g₀ g₁ : P → N} (hg₀ : ∀ x, g₀ x ∈ 𝒩 (-ind x)) (hg₁ : ∀ x, g₁ x ∈ 𝒩 (-ind x))
    (hg₀d : ∀ x, Finsupp.linearCombination A g₀ (m.m x) = dN (g₀ x))
    (hg₁d : ∀ x, Finsupp.linearCombination A g₁ (m.m x) = dN (g₁ x))
    {k : P → N'} (hk : ∀ x, k x ∈ 𝒩' (-ind x - 1))
    (hkd : ∀ x, dN' (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x) = f (g₁ x) - f (g₀ x)) :
    ∃ h : P → N, (∀ x, h x ∈ 𝒩 (-ind x - 1)) ∧
      ∀ x, dN (h x) + rowFiniteSignedMap (𝒜 := 𝒜) h (m.m x) = g₁ x - g₀ x := by
  classical
  let μ : P → ℕ := fun x ↦ (ind x - p₀).toNat
  have hsupp : ∀ x, ∀ y ∈ (m.m x).support, μ y < μ x := fun x y hy ↦
    m.toNat_lt_toNat_of_mem_support hm hp₀ hy
  -- An admissible pair at `x`: the homotopy `h x`, together with a second-order homotopy `l x`
  -- from `k` to `f ∘ h`, given the earlier choices.
  let V : (P → N × N') → P → N × N' → Prop := fun F x v ↦
    v.1 ∈ 𝒩 (-ind x - 1) ∧ v.2 ∈ 𝒩' (-ind x - 1 - 1) ∧
      dN v.1 + rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x) = g₁ x - g₀ x ∧
      k x - f v.1 = dN' v.2 - Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x)
  suffices hGex : ∃ G : P → N × N', ∀ x, V G x (G x) by
    obtain ⟨G, hG⟩ := hGex
    exact ⟨Prod.fst ∘ G, fun x ↦ (hG x).1, fun x ↦ (hG x).2.2.1⟩
  refine exists_forall_of_wellFounded (r := fun y x ↦ μ y < μ x) (measure μ).wf
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) V ?_ ?_
  · -- Admissibility only depends on the choices at the generators in the row.
    rintro x v F F' hFF' ⟨h₁, h₂, h₃, h₄⟩
    have hc : ∀ y ∈ (m.m x).support, F y = F' y := fun y hy ↦ hFF' y (hsupp x y hy)
    refine ⟨h₁, h₂, ?_, ?_⟩
    · rw [← h₃, rowFiniteSignedMap_congr (h' := Prod.fst ∘ F) fun y hy ↦ by simp [hc y hy]]
    · rw [h₄, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      congr 1
      exact Finsupp.sum_congr fun y hy ↦ by simp [hc y hy]
  · intro x F hF
    have hval : ∀ y ∈ (m.m x).support, V F y (F y) := fun y hy ↦ hF y (hsupp x y hy)
    have hrow := m.m_mem_rowFiniteTotalGrading x
    -- The relative cycle `(c, w)` of `f` at `x`.
    have hc : g₁ x - g₀ x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x) ∈ 𝒩 (-ind x) := by
      refine sub_mem (sub_mem (hg₁ x) (hg₀ x)) ?_
      simpa [sub_eq_add_neg] using rowFiniteSignedMap_mem_of_mem_support (j := -1) hrow
        fun y hy ↦ by simpa [sub_eq_add_neg] using (hval y hy).1
    have hw : k x + Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x) ∈ 𝒩' (-ind x - 1) := by
      refine add_mem (hk x) ?_
      have := linearCombination_mem_of_mem_support (g := Prod.snd ∘ F) (j := -1 - 1) hrow
        fun y hy ↦ by simpa [sub_eq_add_neg, add_assoc] using (hval y hy).2.1
      convert this using 2
      ring
    -- The homotopy relation on the row of `x`, from the earlier choices.
    have hH := rowFiniteSignedMap_differential_of_mem_support hN m.m
      (Φ := Finsupp.linearCombination A g₁ - Finsupp.linearCombination A g₀)
      (k := Prod.fst ∘ F) (f := m.m x) fun y hy ↦ by
        rw [LinearMap.sub_apply, Finsupp.linearCombination_single,
          Finsupp.linearCombination_single, one_smul, one_smul]
        exact (hval y hy).2.2.1
    rw [m.differential_row x, map_zero, add_zero, LinearMap.sub_apply, hg₀d, hg₁d] at hH
    -- The second-order relation on the row of `x`, from the earlier choices.
    have hL := rowFiniteSignedMap_eq_of_mem_support hN' m.m
      (θ := k - f ∘ (Prod.fst ∘ F)) (l := Prod.snd ∘ F) (f := m.m x) fun y hy ↦ by
        simpa using (hval y hy).2.2.2
    rw [m.differential_row x, map_zero, sub_zero, rowFiniteSignedMap_sub, LinearMap.sub_apply,
      ← rowFiniteSignedMap_comp] at hL
    have hdc : dN (g₁ x - g₀ x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x)) = 0 := by
      rw [map_sub, map_sub, ← hH, sub_self]
    have hcw : f (g₁ x - g₀ x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x)) =
        dN' (k x + Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x)) := by
      rw [map_add, ← hL, map_sub, map_sub, ← hkd x]
      abel
    obtain ⟨u, v, hu, hv, hdu, huv⟩ := exists_mem_of_forall_exists hN hN' hf hrel
      (n := -ind x) hc (by simpa using hw) hdc hcw
    refine ⟨(u, v), hu, hv, ?_, ?_⟩
    · simp only
      rw [hdu]
      abel
    · calc k x - f u
          = k x + Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x) - f u -
              Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x) := by abel
        _ = f u + dN' v - f u - Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x) := by
              rw [huv]
        _ = dN' v - Finsupp.linearCombination A (Prod.snd ∘ F) (m.m x) := by abel

end RowFiniteTwistingCocycle

/-! ### Semi-free resolutions are unique up to homotopy -/

section Homologous

variable {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}

omit [GradedAlgebra 𝒜] [IsScalarTower R A N] [DirectSum.Decomposition 𝒩] in
/-- An `A`-linear map out of a free module sending each generator to the matching degree is
homogeneous of degree zero. -/
private theorem isHomogeneous_linearCombination {ε : Q → N} (hε : ∀ y, ε y ∈ 𝒩 (-indQ y)) :
    LinearMap.IsHomogeneous (Finsupp.linearCombination A ε) (rowFiniteTotalGrading 𝒜 indQ) 𝒩 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hv ↦ by
    simpa using linearCombination_mem_of_mem_rowFiniteTotalGrading hε hv

/-- Two lifts between semi-free resolutions `ε` and `ε'`, in opposite directions, compose to a
continuation cocycle homotopic to the identity of the target of the second. -/
private theorem nonempty_rowFiniteParametrizedCocycle_refl_comp
    (hmQ : ∀ x y, indQ x ≤ indQ y → mQ.m x y = 0) {q₀ : ℤ} (hq₀ : ∀ x, q₀ ≤ indQ x)
    (hN : IsDGLeftModule hA 𝒩 dN) {ε : P → N} {ε' : Q → N} (hε' : ∀ y, ε' y ∈ 𝒩 (-indQ y))
    (hε'rel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m c = 0 →
      Finsupp.linearCombination A ε' c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m u = c ∧
          Finsupp.linearCombination A ε' u + dN v = w)
    (ν : RowFiniteContinuationCocycle mP mQ) (ν' : RowFiniteContinuationCocycle mQ mP)
    {k : P → N} (hk : ∀ x, k x ∈ 𝒩 (-indP x - 1))
    (hkd : ∀ x, dN (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (mP.m x) =
      ε x - Finsupp.linearCombination A ε' (ν.ν x))
    {k' : Q → N} (hk' : ∀ y, k' y ∈ 𝒩 (-indQ y - 1))
    (hk'd : ∀ y, dN (k' y) + rowFiniteSignedMap (𝒜 := 𝒜) k' (mQ.m y) =
      ε' y - Finsupp.linearCombination A ε (ν'.ν y)) :
    Nonempty (RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mQ hA)
      (ν'.comp ν hA)) := by
  have hNQ := mQ.isDGLeftModule_rowFiniteTwistedDifferential hA
  -- The homotopy `k` on generators extends to the whole free module.
  have hkv (v : P →₀ A) := rowFiniteSignedMap_differential_of_mem_support hN mP.m
    (Φ := Finsupp.linearCombination A ε -
      Finsupp.linearCombination A ε' ∘ₗ Finsupp.linearCombination A ν.ν) (f := v)
    fun x _ ↦ by simpa using hkd x
  obtain ⟨h, hh, hhd⟩ := mQ.exists_homotopy_of_homotopy_comp hmQ hq₀ hNQ hN
    (isHomogeneous_linearCombination hε') hε'rel
    (g₀ := (RowFiniteContinuationCocycle.refl mQ hA).ν) (g₁ := (ν'.comp ν hA).ν)
    (fun y ↦ (RowFiniteContinuationCocycle.refl mQ hA).ν_mem_rowFiniteTotalGrading y)
    (fun y ↦ (ν'.comp ν hA).ν_mem_rowFiniteTotalGrading y)
    (fun y ↦ ((RowFiniteContinuationCocycle.refl mQ hA).continuation y).symm)
    (fun y ↦ ((ν'.comp ν hA).continuation y).symm)
    (k := fun y ↦ -(k' y + rowFiniteSignedMap (𝒜 := 𝒜) k (ν'.ν y)))
    (fun y ↦ neg_mem (add_mem (hk' y) (by
      simpa [sub_eq_add_neg] using rowFiniteSignedMap_mem_of_mem_support (j := -1)
        (ν'.ν_mem_rowFiniteTotalGrading y) fun x _ ↦ by simpa [sub_eq_add_neg] using hk x)))
    (fun y ↦ by
      have hv := hkv (ν'.ν y)
      rw [ν'.continuation y, LinearMap.sub_apply, LinearMap.comp_apply] at hv
      have h₁ : Finsupp.linearCombination A ε' (Finsupp.linearCombination A ν.ν (ν'.ν y)) =
          Finsupp.linearCombination A ε (ν'.ν y) -
            (dN (rowFiniteSignedMap (𝒜 := 𝒜) k (ν'.ν y)) +
              rowFiniteSignedMap (𝒜 := 𝒜) k (Finsupp.linearCombination A ν'.ν (mQ.m y))) := by
        rw [hv]
        abel
      have h₂ : Finsupp.linearCombination A ε (ν'.ν y) =
          ε' y - (dN (k' y) + rowFiniteSignedMap (𝒜 := 𝒜) k' (mQ.m y)) := by
        rw [hk'd y]
        abel
      rw [show (fun y ↦ -(k' y + rowFiniteSignedMap (𝒜 := 𝒜) k (ν'.ν y))) =
          -(k' + fun y ↦ rowFiniteSignedMap (𝒜 := 𝒜) k (ν'.ν y)) from rfl,
        rowFiniteSignedMap_neg, rowFiniteSignedMap_add, LinearMap.neg_apply, LinearMap.add_apply,
        rowFiniteSignedMap_linearCombination,
        RowFiniteContinuationCocycle.comp_ν, RowFiniteContinuationCocycle.refl_ν,
        Finsupp.linearCombination_single, one_smul, h₁, h₂]
      simp only [map_neg, map_add]
      abel)
  exact ⟨{ h := h
           mem_graded := fun y z ↦ by
             have := (mem_rowFiniteTotalGrading_iff _ _).mp (hh y) z
             rwa [show -indQ y - 1 + indQ z = indQ z - indQ y - 1 by ring] at this
           parametrized := hhd }⟩

/-- **Semi-free resolutions are unique up to homotopy.** Let `ε : K_{mP} → N` and
`ε' : K_{mQ} → N` be chain maps from two semi-free row-finite twisted modules, one-sided with
generator indices bounded below, to the same DG left module, whose relative cycles are relative
boundaries. Then `mP` and `mQ` are homologous, so their twisted complexes with coefficients in
any DG right module are homotopy equivalent (`TauCeti.RowFiniteHomologous.homotopyEquiv`). -/
theorem nonempty_rowFiniteHomologous
    (hmP : ∀ x y, indP x ≤ indP y → mP.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ indP x)
    (hmQ : ∀ x y, indQ x ≤ indQ y → mQ.m x y = 0) {q₀ : ℤ} (hq₀ : ∀ x, q₀ ≤ indQ x)
    (hN : IsDGLeftModule hA 𝒩 dN) {ε : P → N} {ε' : Q → N}
    (hε : ∀ x, ε x ∈ 𝒩 (-indP x)) (hε' : ∀ y, ε' y ∈ 𝒩 (-indQ y))
    (hεd : ∀ x, Finsupp.linearCombination A ε (mP.m x) = dN (ε x))
    (hε'd : ∀ y, Finsupp.linearCombination A ε' (mQ.m y) = dN (ε' y))
    (hεrel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      Finsupp.linearCombination A ε c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
          Finsupp.linearCombination A ε u + dN v = w)
    (hε'rel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m c = 0 →
      Finsupp.linearCombination A ε' c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m u = c ∧
          Finsupp.linearCombination A ε' u + dN v = w) :
    Nonempty (RowFiniteHomologous hA mP mQ) := by
  have hNP := mP.isDGLeftModule_rowFiniteTwistedDifferential hA
  have hNQ := mQ.isDGLeftModule_rowFiniteTwistedDifferential hA
  obtain ⟨ν, k, hν, hk, hνd, hkd⟩ := mP.exists_lift hmP hp₀ hNQ hN
    (isHomogeneous_linearCombination hε') hε'rel hε hεd
  obtain ⟨ν', k', hν', hk', hν'd, hk'd⟩ := mQ.exists_lift hmQ hq₀ hNP hN
    (isHomogeneous_linearCombination hε) hεrel hε' hε'd
  let c : RowFiniteContinuationCocycle mP mQ :=
    { ν := ν
      mem_graded := fun x y ↦ by
        simpa only [neg_add_eq_sub] using (mem_rowFiniteTotalGrading_iff _ _).mp (hν x) y
      continuation := fun x ↦ (hνd x).symm }
  let c' : RowFiniteContinuationCocycle mQ mP :=
    { ν := ν'
      mem_graded := fun y x ↦ by
        simpa only [neg_add_eq_sub] using (mem_rowFiniteTotalGrading_iff _ _).mp (hν' y) x
      continuation := fun y ↦ (hν'd y).symm }
  obtain ⟨homQ⟩ := nonempty_rowFiniteParametrizedCocycle_refl_comp hmQ hq₀ hN hε' hε'rel c c'
    hk hkd hk' hk'd
  obtain ⟨homP⟩ := nonempty_rowFiniteParametrizedCocycle_refl_comp hmP hp₀ hN hε hεrel c' c
    hk' hk'd hk hkd
  exact ⟨⟨c, c', homP, homQ⟩⟩

/-- **A quasi-isomorphism of semi-free twisted modules is a homotopy equivalence.** Let `mP` and
`mQ` be one-sided with generator indices bounded below, and let `ν` be a continuation cocycle
from `mP` to `mQ` whose relative cycles are relative boundaries. Then `ν` is part of a
homotopy equivalence: there is a continuation cocycle back with both composites homotopic to the
identity. -/
theorem RowFiniteContinuationCocycle.exists_rowFiniteHomologous_ν_eq
    (hmP : ∀ x y, indP x ≤ indP y → mP.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ indP x)
    (hmQ : ∀ x y, indQ x ≤ indQ y → mQ.m x y = 0) {q₀ : ℤ} (hq₀ : ∀ x, q₀ ≤ indQ x)
    (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      Finsupp.linearCombination A ν.ν c =
        rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m w →
      ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
        Finsupp.linearCombination A ν.ν u +
          rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m v = w) :
    ∃ H : RowFiniteHomologous hA mP mQ, H.ν = ν := by
  have hNP := mP.isDGLeftModule_rowFiniteTwistedDifferential hA
  have hNQ := mQ.isDGLeftModule_rowFiniteTwistedDifferential hA
  -- Lift the identity of `K_{mQ}` along `ν`.
  obtain ⟨ν', k', hν', hk', hν'd, hk'd⟩ := mQ.exists_lift hmQ hq₀ hNP hNQ
    (isHomogeneous_linearCombination ν.ν_mem_rowFiniteTotalGrading) hν
    (RowFiniteContinuationCocycle.refl mQ hA).ν_mem_rowFiniteTotalGrading
    fun y ↦ ((RowFiniteContinuationCocycle.refl mQ hA).continuation y).symm
  let c' : RowFiniteContinuationCocycle mQ mP :=
    { ν := ν'
      mem_graded := fun y x ↦ by
        simpa only [neg_add_eq_sub] using (mem_rowFiniteTotalGrading_iff _ _).mp (hν' y) x
      continuation := fun y ↦ (hν'd y).symm }
  have homQ :
      RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mQ hA) (c'.comp ν hA) :=
    { h := -k'
      mem_graded := fun y z ↦ by
        have := neg_mem ((mem_rowFiniteTotalGrading_iff _ _).mp (hk' y) z)
        rwa [show -indQ y - 1 + indQ z = indQ z - indQ y - 1 by ring] at this
      parametrized := fun y ↦ by
        have := hk'd y
        rw [Pi.neg_apply, map_neg, rowFiniteSignedMap_neg, LinearMap.neg_apply, ← neg_add, this,
          neg_sub, RowFiniteContinuationCocycle.comp_ν] }
  have hrefl : ∀ x, Finsupp.linearCombination A (RowFiniteContinuationCocycle.refl mQ hA).ν
      (ν.ν x) = ν.ν x := fun x ↦ by
    have := congrArg (fun μ : RowFiniteContinuationCocycle mP mQ ↦ μ.ν x) (ν.comp_refl hA)
    simpa only [RowFiniteContinuationCocycle.comp_ν] using this
  obtain ⟨homP⟩ := nonempty_rowFiniteParametrizedCocycle_refl_comp hmP hp₀ hNQ
    (ε := (RowFiniteContinuationCocycle.refl mQ hA).ν) (ε' := ν.ν) ν.ν_mem_rowFiniteTotalGrading
    hν c' ν
    (k := k') hk' hk'd (k' := 0) (fun _ ↦ zero_mem _)
    (fun x ↦ by simp [hrefl, rowFiniteSignedMap_apply])
  exact ⟨⟨ν, c', homP, homQ⟩, rfl⟩

end Homologous

end TauCeti
