/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.CompactSupport
public import TauCeti.RepresentationTheory.Smooth.Basic
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The translation representation on locally constant functions with compact support

Let a topological group `G` act on a topological space `X`, by homeomorphisms. Then `G` acts on
the `R`-module `C_c^∞(X, M)` of locally constant functions with compact support
(`LocallyConstant.compactlySupported`) by translation, `(g • f)(x) = f(g⁻¹ • x)`. When the action
on `X` is jointly continuous this representation is smooth: for a test function `f`, the tube
lemma over the compact support of `f` gives a neighbourhood `U` of `1` with `f(g • y) = f(y)` and
`f(g⁻¹ • y) = f(y)` for every `g ∈ U` and every `y` in the support, and then `U` fixes `f`.

## Main definitions

* `TauCeti.compactlySupportedRep R G X M`: the translation representation of `G` on
  `C_c^∞(X, M)`.

## Main results

* `TauCeti.compactlySupportedRep_apply_coe`: `(g • f)(x) = f(g⁻¹ • x)`.
* `TauCeti.isSmooth_compactlySupportedRep`: for a continuous action, the translation
  representation is smooth.
* `TauCeti.support_compactlySupportedRep_apply`: translation by `g` moves the support by `g`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.2, Proposition 2, p. 8.
-/

public section

noncomputable section

open Function Pointwise

namespace TauCeti

variable (R G X M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Group G]
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- **The translation representation** of `G` on `C_c^∞(X, M)`: `(g • f)(x) = f(g⁻¹ • x)`. -/
def compactlySupportedRep : Representation R G (LocallyConstant.compactlySupported R X M) where
  toFun g := (LocallyConstant.comapₗ R ⟨(g⁻¹ • ·), continuous_const_smul _⟩).restrict
    fun _ hf ↦ LocallyConstant.mem_compactlySupported.2 <|
      (LocallyConstant.mem_compactlySupported.1 hf).comp_homeomorph (Homeomorph.smul g⁻¹)
  map_one' := LinearMap.ext fun _ ↦ Subtype.ext <| LocallyConstant.ext fun x ↦ by simp
  map_mul' g h := LinearMap.ext fun f ↦ Subtype.ext <| LocallyConstant.ext fun x ↦ by
    simp [mul_smul]

variable {R G X M}

@[simp]
theorem compactlySupportedRep_apply_coe (g : G) (f : LocallyConstant.compactlySupported R X M)
    (x : X) : (compactlySupportedRep R G X M g f : LocallyConstant X M) x = f.val (g⁻¹ • x) :=
  (rfl)

/-- Translation by `g` sends the value at `x` to the value at `g • x`. -/
theorem compactlySupportedRep_apply_smul (g : G) (f : LocallyConstant.compactlySupported R X M)
    (x : X) : (compactlySupportedRep R G X M g f : LocallyConstant X M) (g • x) = f.val x := by
  simp

/-- **Translation by `g` moves the support by `g`.** -/
theorem support_compactlySupportedRep_apply (g : G)
    (f : LocallyConstant.compactlySupported R X M) :
    support (compactlySupportedRep R G X M g f : LocallyConstant X M) = g • support f.val :=
  support_comp_inv_smul g f.val

/-- An element acting trivially on `X` acts trivially on `C_c^∞(X, M)`. -/
theorem compactlySupportedRep_apply_eq_one {g : G} (hg : ∀ x : X, g • x = x) :
    compactlySupportedRep R G X M g = 1 := by
  have hg' (x : X) : g⁻¹ • x = x := by
    rw [inv_smul_eq_iff, hg]
  exact LinearMap.ext fun f ↦ Subtype.ext <| LocallyConstant.ext fun x ↦ by simp [hg']

/-- For a continuous action of a topological group, every test function is fixed by a
neighbourhood of `1`: **the translation representation is smooth**. -/
instance isSmooth_compactlySupportedRep [TopologicalSpace G] [IsTopologicalGroup G]
    [ContinuousSMul G X] : (compactlySupportedRep R G X M).IsSmooth where
  isOpen_stabilizer f := by
    set φ : LocallyConstant X M := f.val
    have hK : IsCompact (support φ) := by
      rw [← LocallyConstant.tsupport_eq_support]
      exact LocallyConstant.mem_compactlySupported.1 f.property
    -- The pairs `(g, y)` with `φ(g • y) = φ y = φ(g⁻¹ • y)` form an open set.
    let n : Set (G × X) := {p | φ (p.1 • p.2) = φ p.2 ∧ φ (p.1⁻¹ • p.2) = φ p.2}
    have hn : IsOpen n := by
      have h₁ : IsLocallyConstant fun p : G × X ↦ (φ (p.1 • p.2), φ p.2, φ (p.1⁻¹ • p.2)) :=
        ((φ.isLocallyConstant.comp_continuous continuous_smul).prodMk
          ((φ.isLocallyConstant.comp_continuous continuous_snd).prodMk
            (φ.isLocallyConstant.comp_continuous
              ((continuous_inv.comp continuous_fst).smul continuous_snd))))
      -- By definition `n` is the preimage of `{t | t.1 = t.2.1 ∧ t.2.2 = t.2.1}` under this map.
      exact h₁ {t | t.1 = t.2.1 ∧ t.2.2 = t.2.1}
    obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ := generalized_tube_lemma
      (isCompact_singleton (x := (1 : G))) hK hn fun ⟨g, y⟩ ⟨hg, _⟩ ↦ by
        obtain rfl : g = 1 := hg
        simp [n]
    refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hu.mem_nhds (h1u rfl))
      fun g hg ↦ ?_)
    rw [SetLike.mem_coe, Representation.mem_stabilizer]
    refine Subtype.ext <| LocallyConstant.ext fun y ↦ ?_
    rw [compactlySupportedRep_apply_coe]
    by_cases hy : y ∈ support φ
    · exact (huv (a := (g, y)) ⟨hg, hKv hy⟩).2
    by_cases hy' : g⁻¹ • y ∈ support φ
    · have := (huv (a := (g, g⁻¹ • y)) ⟨hg, hKv hy'⟩).1
      rw [smul_inv_smul] at this
      exact this.symm
    · rw [notMem_support.1 hy, notMem_support.1 hy']

end TauCeti
