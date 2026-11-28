/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.RingTheory.NovikovModule.Residue
public import TauCeti.RingTheory.NovikovModule.Specialization
public import TauCeti.RingTheory.NovikovModule.Topology
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The completed complex of a Laurent differential over the Novikov ring

Let the generators be a finite disjoint union `Σ i, P i` of torsors under a group `H` of periods,
with a potential `F` on which a period `h` acts by `F (h +ᵥ p) = F p - N h`, and let `Λ` be the
Novikov ring `NovikovSeries R H N`. A Laurent kernel (`TauCeti.NovikovModule.IsLaurentKernel`) is
a homogeneous matrix of the finite Laurent model: it is invariant under the periods and its
outputs are finite combinations. This file extends such matrices from the finite Laurent model to
the completed modules over `Λ`.

The outputs of a Laurent kernel lie in finitely many orbits of the periods, so its potential
increase is bounded (`TauCeti.NovikovModule.IsLaurentKernel.exists_potential_le`), and it acts on
completed combinations by a `Λ`-linear map (`TauCeti.NovikovModule.IsLaurentKernel.novikovMap`).
This map shifts the potential filtration by a fixed amount
(`TauCeti.NovikovModule.IsLaurentKernel.exists_novikovMap_mem_potentialFiltration`), so it is
continuous, and composites of these maps are given by composites of kernels. The degrees carried
by a Laurent kernel play no role in its map: an invariant kernel with finite outputs is a Laurent
kernel for the degree on `Unit`.

The integer degrees of the generators are not bounded on a completed combination, so the
completion is graded by a degree `d` that is constant on the orbits, for instance an integer
degree read modulo a multiple of all its period shifts. Then the completed module is the direct
sum of its homogeneous pieces as a `Λ`-module (`TauCeti.NovikovModule.isInternal_novikovGradeBy`),
each of them free over `Λ` on the orbits of that degree
(`TauCeti.NovikovModule.novikovGradeByBasis`). A Laurent differential `δ` of degree `1` with
`δ ∘ δ = 0` gives the *Novikov complex*
(`TauCeti.NovikovModule.novikovComplex`), the complex of `Λ`-modules whose term of degree `a`
is the piece of degree `a` and whose differential is the map of `δ`. Laurent chain maps `Φ` and
`Ψ` of degree `0`, inverse to each other up to Laurent homotopies of degree `-1`, give a homotopy
equivalence of Novikov complexes (`TauCeti.NovikovModule.novikovComplexHomotopyEquiv`). It has
the same hypotheses as the cyclic specialization `t ↦ 1` of the same data,
`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv`, which is defined on the finite Laurent model
only: in the completion a series `1 - e^h` of positive period is a unit, so no specialization
`t ↦ 1` extends to `Λ`.

In capped Hamiltonian Floer theory on a monotone target the generators are the capped
contractible periodic orbits, `H` is the period group, the potential is the action functional, and
the degree is the Conley–Zehnder index modulo twice the minimal Chern number. The Floer and Morse
differentials, the continuation and PSS maps and their homotopies are Laurent kernels, and the
Novikov complexes and their homotopy equivalence are the completed Floer complex over the Novikov
ring, graded modulo twice the minimal Chern number, and its PSS comparison with the Morse complex
with Novikov coefficients.

## Main definitions

* `TauCeti.NovikovModule.IsLaurentKernel.novikovMap`: the `Λ`-linear map of a Laurent kernel.
* `TauCeti.NovikovModule.gradedNovikovMap`: its restriction to homogeneous pieces whose degrees
  differ by the degree of the kernel.
* `TauCeti.NovikovModule.novikovGradeByBasis`: the basis of a homogeneous piece given by the
  lifts of the orbits of that degree.
* `TauCeti.NovikovModule.novikovComplex`: the Novikov complex of a Laurent differential.
* `TauCeti.NovikovModule.novikovComplexXEquiv`, `TauCeti.NovikovModule.novikovComplexBasis`: its
  term of degree `a` is the piece of degree `a`, free on the orbits of degree `a`; so its terms
  are finite free modules over the Novikov ring (the `Module.Free` and `Module.Finite`
  instances).
* `TauCeti.NovikovModule.novikovComplexHom`: the chain map of a Laurent chain map.
* `TauCeti.NovikovModule.novikovComplexHomotopy`: the homotopy given by a Laurent homotopy.
* `TauCeti.NovikovModule.novikovComplexHomotopyEquiv`: the homotopy equivalence of Novikov
  complexes given by Laurent chain maps inverse to each other up to Laurent homotopies.

## Main results

* `TauCeti.NovikovModule.IsLaurentKernel.exists_potential_le`: a Laurent kernel between finite
  unions of torsors with equivariant potentials obeys a potential bound, and so does a composite
  of two of them (`TauCeti.NovikovModule.IsLaurentKernel.exists_potential_le_kernelComp`).
* `TauCeti.NovikovModule.IsLaurentKernel.novikovMap_novikovMap_apply_val`: composites of maps of
  Laurent kernels are given by composites of kernels.
* `TauCeti.NovikovModule.IsLaurentKernel.novikovMap_novikovMap_sub_eq`: a Laurent kernel homotopy
  gives a homotopy of maps.
* `TauCeti.NovikovModule.IsLaurentKernel.exists_novikovMap_mem_potentialFiltration`,
  `TauCeti.NovikovModule.IsLaurentKernel.continuous_novikovMap`: the map shifts the potential
  filtration by a fixed amount, and is continuous.

## Implementation notes

`TauCeti.gradedCochainComplex` assembles a `ℤ`-indexed family of submodules with a differential
into a cochain complex. The residue grading is indexed by a general additive type such as
`ZMod n`, so the Novikov complex and its chain maps are assembled with Mathlib's
`CochainComplex.of` and `CochainComplex.ofHom`, which allow any such index type. Its terms are
reached through `TauCeti.NovikovModule.novikovComplexXEquiv`, and its differential, chain maps and
homotopies through the lemmas `coe_novikovComplexXEquiv_*`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progr. Math. 133 (1995), 483–524.
* S. Piunikhin, D. Salamon, M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

noncomputable section

open Function CategoryTheory

namespace TauCeti

namespace NovikovModule

section LaurentMap

variable {R H A ι₁ ι₀ ι₂ : Type*} [Semiring R] [AddGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*} {P₂ : ι₂ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)] [∀ l, AddTorsor H (P₂ l)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ} {F₂ : (Σ l, P₂ l) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hF₂ : ∀ l h (p : P₂ l), F₂ ⟨l, h +ᵥ p⟩ = F₂ ⟨l, p⟩ - N h)
  [Add A] {d₁ : (Σ i, P₁ i) → A} {d₀ : (Σ k, P₀ k) → A} {d₂ : (Σ l, P₂ l) → A} {c c' : A}
  {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R} {m' : (Σ k, P₀ k) → (Σ l, P₂ l) → R}

namespace IsLaurentKernel

/-- The outputs of a Laurent kernel are finite combinations, so they are completed
combinations. -/
theorem mem_novikovModule (hm : IsLaurentKernel d₁ d₀ c m) (p : Σ i, P₁ i) :
    m p ∈ NovikovModule R F₀ :=
  mem_of_finite_support (hm.finite_support p)

include hF₁ hF₀ in
/-- **A Laurent kernel obeys a potential bound.** For equivariant potentials with the same period
homomorphism, the potential increase `F₀ q - F₁ p` along a nonzero coefficient `m p q` is
unchanged by translating `p` and `q` by the same period. So it takes only the finitely many
values it takes at the outputs of reference generators of the finitely many input orbits. -/
theorem exists_potential_le [Finite ι₁] (hm : IsLaurentKernel d₁ d₀ c m) :
    ∃ C, ∀ p q, m p q ≠ 0 → F₀ q ≤ F₁ p + C := by
  let r := fun i => Classical.arbitrary (P₁ i)
  have hfin : (⋃ i, (fun q => F₀ q - F₁ ⟨i, r i⟩) '' support (m ⟨i, r i⟩)).Finite :=
    Set.finite_iUnion fun i => (hm.finite_support _).image _
  obtain ⟨C, hC⟩ := hfin.bddAbove
  refine ⟨C, fun ⟨i, p⟩ ⟨k, q⟩ h => ?_⟩
  -- Translate `p` back to the reference generator `r i`, and `q` along with it.
  set g := p -ᵥ r i
  have h' : m ⟨i, r i⟩ ⟨k, -g +ᵥ q⟩ ≠ 0 := by
    rwa [← hm.apply_vadd_vadd g, vadd_neg_vadd, vsub_vadd]
  have hle := hC (Set.mem_iUnion.2 ⟨i, ⟨_, h', rfl⟩⟩)
  have hp := hF₁ i g (r i)
  rw [vsub_vadd] at hp
  have hq := hF₀ k (-g) q
  simp only [map_neg, sub_neg_eq_add] at hq hle
  rw [hq] at hle
  linarith

include hF₁ hF₀ hF₂ in
/-- **A composite of Laurent kernels obeys a potential bound.** Along a nonzero coefficient of the
composite kernel the potential increase is at most the sum of the bounds of the two kernels. -/
theorem exists_potential_le_kernelComp [Finite ι₁] [Finite ι₀] (hm : IsLaurentKernel d₁ d₀ c m)
    (hm' : IsLaurentKernel d₀ d₂ c' m') :
    ∃ C, ∀ p q, kernelComp m m' p q ≠ 0 → F₂ q ≤ F₁ p + C := by
  obtain ⟨C, hC⟩ := hm.exists_potential_le hF₁ hF₀
  obtain ⟨C', hC'⟩ := hm'.exists_potential_le hF₀ hF₂
  exact ⟨C + C', fun p q h => by
    linarith [potential_le_of_kernelComp_ne_zero (hC p) (hC' · q) h]⟩

include hF₀ hF₂ in
/-- The outputs of a composite of Laurent kernels are completed combinations. -/
theorem kernelComp_mem_novikovModule [Finite ι₀] (hm : IsLaurentKernel d₁ d₀ c m)
    (hm' : IsLaurentKernel d₀ d₂ c' m') (p : Σ i, P₁ i) :
    kernelComp m m' p ∈ NovikovModule R F₂ :=
  kernelComp_mem (hm'.exists_potential_le hF₀ hF₂).choose_spec hm'.mem_novikovModule
    (hm.mem_novikovModule p)

variable [Finite ι₁] [Finite ι₀] [Finite ι₂]

/-- **The map of a Laurent kernel on completed combinations.** The coefficient of `q` in the image
of `a` is the finite sum `∑ a(p) m(p, q)` (`novikovMap_apply_val`). It is linear over the Novikov
ring, for the Novikov module structures of `TauCeti.NovikovModule.module`. -/
def novikovMap (hm : IsLaurentKernel d₁ d₀ c m) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₀ :=
  novikovKernelMap hF₁ hF₀ (hm.exists_potential_le hF₁ hF₀).choose_spec
    hm.mem_novikovModule hm.apply_vadd_vadd

/-- The map of a Laurent kernel is the kernel map of `m`, for any potential bound. -/
theorem novikovMap_apply (hm : IsLaurentKernel d₁ d₀ c m) {C : ℝ}
    (hC : ∀ p q, m p q ≠ 0 → F₀ q ≤ F₁ p + C) (a : NovikovModule R F₁) :
    hm.novikovMap hF₁ hF₀ a =
      kernelMap hC hm.mem_novikovModule a :=
  Subtype.ext <| funext fun q => by
    rw [novikovMap, novikovKernelMap_apply, kernelMap_apply_val, kernelMap_apply_val]

/-- The coefficients of the image of a completed combination under the map of a Laurent
kernel. -/
@[simp]
theorem novikovMap_apply_val (hm : IsLaurentKernel d₁ d₀ c m) (a : NovikovModule R F₁)
    (q : Σ k, P₀ k) : (hm.novikovMap hF₁ hF₀ a).val q = ∑ᶠ p, a.val p * m p q := by
  rw [novikovMap, novikovKernelMap_apply, kernelMap_apply_val]

/-- **Composites of maps of Laurent kernels.** Applying the maps of `m` and then of `m'` is
applying the composite kernel `∑ m(p, q) m'(q, ·)`. -/
theorem novikovMap_novikovMap_apply_val (hm : IsLaurentKernel d₁ d₀ c m)
    (hm' : IsLaurentKernel d₀ d₂ c' m') (a : NovikovModule R F₁) (q : Σ l, P₂ l) :
    (hm'.novikovMap hF₀ hF₂ (hm.novikovMap hF₁ hF₀ a)).val q =
      ∑ᶠ p, a.val p * kernelComp m m' p q := by
  obtain ⟨C, hC⟩ := hm.exists_potential_le hF₁ hF₀
  obtain ⟨C', hC'⟩ := hm'.exists_potential_le hF₀ hF₂
  obtain ⟨C'', hCC⟩ := hm.exists_potential_le_kernelComp hF₁ hF₀ hF₂ hm'
  rw [hm.novikovMap_apply hF₁ hF₀ hC, hm'.novikovMap_apply hF₀ hF₂ hC',
    kernelMap_kernelMap hC hm.mem_novikovModule hC' hm'.mem_novikovModule hCC
      (hm.kernelComp_mem_novikovModule hF₀ hF₂ hm'), kernelMap_apply_val]

end IsLaurentKernel

end LaurentMap

section LaurentMapRing

variable {R H A ι₁ ι₀ : Type*} [Ring R] [AddGroup H] {N : H →+ ℝ} [Finite ι₁] [Finite ι₀]
  {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  [Add A] {d₁ : (Σ i, P₁ i) → A} {d₀ : (Σ k, P₀ k) → A} {c c' : A}
  {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R}

namespace IsLaurentKernel

/-- **Kernel homotopies give homotopies of maps.** If Laurent kernels `Φ`, `Ψ`, `K` and `δ`
satisfy `Φ Ψ - 1 = K δ + δ K` as composite kernels, then the maps of `Φ` and `Ψ` are inverse to
each other up to the homotopy `K`: `Ψ (Φ a) - a = δ (K a) + K (δ a)`. -/
theorem novikovMap_novikovMap_sub_eq [DecidableEq (Σ i, P₁ i)] {e e' : A}
    {Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R} {K δ : (Σ i, P₁ i) → (Σ i, P₁ i) → R}
    (hm : IsLaurentKernel d₁ d₀ c m) (hΨ : IsLaurentKernel d₀ d₁ c' Ψ)
    (hK : IsLaurentKernel d₁ d₁ e K) (hδ : IsLaurentKernel d₁ d₁ e' δ)
    (hmΨ : ∀ p q, kernelComp m Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ p q + kernelComp δ K p q) (a : NovikovModule R F₁) :
    hΨ.novikovMap hF₀ hF₁ (hm.novikovMap hF₁ hF₀ a) - a =
      hδ.novikovMap hF₁ hF₁ (hK.novikovMap hF₁ hF₁ a) +
        hK.novikovMap hF₁ hF₁ (hδ.novikovMap hF₁ hF₁ a) := by
  obtain ⟨CC, hCC⟩ := hm.exists_potential_le_kernelComp hF₁ hF₀ hF₁ hΨ
  obtain ⟨Ck, hCk⟩ := hK.exists_potential_le hF₁ hF₁
  obtain ⟨Cδ, hCδ⟩ := hδ.exists_potential_le hF₁ hF₁
  have hfin := hm.kernelComp_mem_novikovModule hF₀ hF₁ hΨ
  -- The composite of the two maps and the identity are kernel maps, and the difference of their
  -- kernels is the kernel homotopy.
  have hcomp : hΨ.novikovMap hF₀ hF₁ (hm.novikovMap hF₁ hF₀ a) = kernelMap hCC hfin a :=
    Subtype.ext <| funext fun q => by
      rw [hm.novikovMap_novikovMap_apply_val hF₁ hF₀ hF₁ hΨ, kernelMap_apply_val]
  have hid : kernelMap
      (fun _ _ h => potential_le_of_diagonal_ne_zero (F := F₁) (s := fun _ => 1) h)
      (diagonal_mem fun _ => (1 : R)) a = a := by
    rw [kernelMap_eq_id, LinearMap.id_apply]
  rw [hcomp, ← congrArg (kernelMap hCC hfin a - ·) hid,
    kernelMap_sub_kernelMap hCC hfin _ _ hCk hK.mem_novikovModule hCδ
      hδ.mem_novikovModule hCδ hδ.mem_novikovModule hmΨ]
  simp only [hK.novikovMap_apply hF₁ hF₁ hCk, hδ.novikovMap_apply hF₁ hF₁ hCδ]

/-- **The map of a Laurent kernel shifts the potential filtration.** There is a constant `C` such
that the map sends the combinations supported in potentials at most `D` to those supported in
potentials at most `D + C`, for every `D`. -/
theorem exists_novikovMap_mem_potentialFiltration (hm : IsLaurentKernel d₁ d₀ c m) :
    ∃ C, ∀ D (a : NovikovModule R F₁), a ∈ potentialFiltration R F₁ D →
      hm.novikovMap hF₁ hF₀ a ∈ potentialFiltration R F₀ (D + C) :=
  let ⟨C, hC⟩ := hm.exists_potential_le hF₁ hF₀
  ⟨C, fun _ a ha => hm.novikovMap_apply hF₁ hF₀ hC a ▸ kernelMap_mem_potentialFiltration hC _ ha⟩

/-- The map of a Laurent kernel is continuous for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_novikovMap (hm : IsLaurentKernel d₁ d₀ c m) :
    Continuous (hm.novikovMap hF₁ hF₀) := by
  obtain ⟨C, hC⟩ := hm.exists_potential_le hF₁ hF₀
  have h : ⇑(hm.novikovMap hF₁ hF₀) = kernelMap hC _ := funext (hm.novikovMap_apply hF₁ hF₀ hC)
  exact h ▸ continuous_kernelMap _ _

end IsLaurentKernel

end LaurentMapRing

section GradedMap

variable {R H A ι₁ ι₀ : Type*} [Semiring R] [AddGroup H] {N : H →+ ℝ} [Finite ι₁] [Finite ι₀]
  {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  [Add A] {d₁ : (Σ i, P₁ i) → A} {d₀ : (Σ k, P₀ k) → A}
  (hd₁ : ∀ i (g : H) (p : P₁ i), d₁ ⟨i, g +ᵥ p⟩ = d₁ ⟨i, p⟩)
  (hd₀ : ∀ k (g : H) (q : P₀ k), d₀ ⟨k, g +ᵥ q⟩ = d₀ ⟨k, q⟩)
  {c : A} {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R}

/-- The map of a Laurent kernel of degree `c` restricted to the piece of degree `a` and the piece
of degree `b = a + c`, which contains its image. -/
def gradedNovikovMap (hm : IsLaurentKernel d₁ d₀ c m) {a b : A} (h : a + c = b) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    novikovGradeBy (R := R) hF₁ hd₁ a →ₗ[NovikovSeries R H N] novikovGradeBy (R := R) hF₀ hd₀ b :=
  letI := module (R := R) hF₁
  letI := module (R := R) hF₀
  (hm.novikovMap hF₁ hF₀).restrict fun x hx => by
    obtain ⟨C, hC⟩ := hm.exists_potential_le hF₁ hF₀
    rw [mem_novikovGradeBy, hm.novikovMap_apply hF₁ hF₀ hC, ← h]
    exact kernelMap_mem_gradeBy _ _ hm.degree_eq ((mem_novikovGradeBy hF₁ hd₁).1 hx)

variable {hF₁ hF₀ hd₁ hd₀}

/-- The restriction of the map of a Laurent kernel to homogeneous pieces is the map itself. -/
@[simp]
theorem coe_gradedNovikovMap_apply (hm : IsLaurentKernel d₁ d₀ c m) {a b : A} (h : a + c = b)
    (x : novikovGradeBy (R := R) hF₁ hd₁ a) :
    (gradedNovikovMap hF₁ hF₀ hd₁ hd₀ hm h x : NovikovModule R F₀) =
      hm.novikovMap hF₁ hF₀ x := by
  simp only [gradedNovikovMap, LinearMap.coe_restrict_apply]

end GradedMap

section Basis

variable {R H D ι : Type*} [Semiring R] [AddGroup H] {N : H →+ ℝ} [Finite ι] {P : ι → Type*}
  [∀ i, AddTorsor H (P i)] {F : (Σ i, P i) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
  {d : (Σ i, P i) → D} (hd : ∀ i (g : H) (p : P i), d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩)

/-- For a degree constant on orbits, the homogeneous piece of degree `k` is spanned over the
Novikov ring by the basis vectors of the orbits of degree `k`. -/
theorem novikovGradeBy_eq_span (r : ∀ i, P i) (k : D) :
    letI := module (R := R) hF
    novikovGradeBy (R := R) hF hd k =
      Submodule.span (NovikovSeries R H N)
        (Set.range fun i : {i // orbitDegree d i = k} => basis (R := R) hF r i) := by
  let := module (R := R) hF
  have := Fintype.ofFinite ι
  refine le_antisymm (fun a ha => ?_) (Submodule.span_le.2 ?_)
  · -- A homogeneous combination has zero coordinates in the orbits of other degrees.
    rw [← (basis hF r).sum_repr a]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : orbitDegree d i = k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · have h0 : (basis hF r).repr a i = 0 := by
        rw [basis_repr_apply]
        ext g
        rw [coordinates_coeff, NovikovSeries.coeff_zero]
        by_contra hg
        exact hi (by
          rw [← mem_gradeBy_iff.1 ((mem_novikovGradeBy hF hd).1 ha) _ hg, orbitDegree_apply hd])
      rw [h0, zero_smul]
      exact Submodule.zero_mem _
  · rintro _ ⟨⟨i, rfl⟩, rfl⟩
    exact (mem_novikovGradeBy hF hd).2 <| by
      simpa only [orbitDegree_apply hd (r i)] using basis_mem_gradeBy hF r i

/-- **The homogeneous pieces are free.** For a degree constant on orbits, the homogeneous piece
of degree `k` is free over the Novikov ring, with basis the chosen lifts of the orbits of degree
`k`. -/
def novikovGradeByBasis (r : ∀ i, P i) (k : D) :
    letI := module (R := R) hF
    Module.Basis {i // orbitDegree d i = k} (NovikovSeries R H N)
      (novikovGradeBy (R := R) hF hd k) :=
  letI := module (R := R) hF
  (Module.Basis.span (((basis hF r).linearIndependent.comp _ Subtype.val_injective))).map
    (LinearEquiv.ofEq _ _ (novikovGradeBy_eq_span hF hd r k).symm)

/-- The basis vector of an orbit of degree `k` is the basis vector of the completed module. -/
@[simp]
theorem coe_novikovGradeByBasis_apply (r : ∀ i, P i) (k : D) (i : {i // orbitDegree d i = k}) :
    (novikovGradeByBasis (R := R) hF hd r k i : NovikovModule R F) = basis hF r i := by
  simp [novikovGradeByBasis]

end Basis

section Complex

universe u v w

variable {R : Type u} [Ring R] {H A : Type*} [AddGroup H] {N : H →+ ℝ}
  [AddRightCancelSemigroup A] [One A] [DecidableEq A] {ι : Type v} [Finite ι] {P : ι → Type w}
  [∀ i, AddTorsor H (P i)] {F : (Σ i, P i) → ℝ}

variable (R) in
/-- The *Novikov complex* of a Laurent differential `δ` of degree `1` with `δ ∘ δ = 0`, for a
degree `d` constant on the orbits: the complex of modules over the Novikov ring whose term of
degree `a` is the piece of degree `a` of the completed module
(`TauCeti.NovikovModule.novikovComplexXEquiv`), free on the orbits of degree `a`
(`TauCeti.NovikovModule.novikovComplexBasis`), and whose differential is the map of `δ`
(`TauCeti.NovikovModule.coe_novikovComplexXEquiv_d_apply`). -/
def novikovComplex (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
    (d : (Σ i, P i) → A) (hd : ∀ i (g : H) (p : P i), d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩)
    (δ : (Σ i, P i) → (Σ i, P i) → R) (hδ : IsLaurentKernel d d 1 δ)
    (hδδ : ∀ p q, kernelComp δ δ p q = 0) :
    CochainComplex (ModuleCat.{max u v w} (NovikovSeries R H N)) A :=
  letI := module (R := R) hF
  CochainComplex.of (fun a => ModuleCat.of _ (novikovGradeBy (R := R) hF hd a))
    (fun a => ModuleCat.ofHom (gradedNovikovMap hF hF hd hd hδ rfl)) fun a => by
      ext x : 2
      refine Subtype.ext (Subtype.ext ?_)
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        coe_gradedNovikovMap_apply]
      ext q
      rw [hδ.novikovMap_novikovMap_apply_val hF hF hF hδ x q]
      simp [hδδ]

variable {hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h} {d : (Σ i, P i) → A}
  {hd : ∀ i (g : H) (p : P i), d ⟨i, g +ᵥ p⟩ = d ⟨i, p⟩} {δ : (Σ i, P i) → (Σ i, P i) → R}
  {hδ : IsLaurentKernel d d 1 δ} {hδδ : ∀ p q, kernelComp δ δ p q = 0}

variable (R hF d hd δ hδ hδδ) in
/-- The term of degree `a` of the Novikov complex is the piece of degree `a` of the completed
module. -/
def novikovComplexXEquiv (a : A) :
    letI := module (R := R) hF
    (novikovComplex R hF d hd δ hδ hδδ).X a ≃ₗ[NovikovSeries R H N]
      novikovGradeBy (R := R) hF hd a :=
  letI := module (R := R) hF
  LinearEquiv.refl _ _

/-- The differential of the Novikov complex is the map of the Laurent differential. -/
@[simp]
theorem coe_novikovComplexXEquiv_d_apply {a b : A} (h : a + 1 = b)
    (x : (novikovComplex R hF d hd δ hδ hδδ).X a) :
    (novikovComplexXEquiv R hF d hd δ hδ hδδ b (((novikovComplex R hF d hd δ hδ hδδ).d a b).hom x) :
      NovikovModule R F) =
        hδ.novikovMap hF hF (novikovComplexXEquiv R hF d hd δ hδ hδδ a x : NovikovModule R F) := by
  subst h
  dsimp only [novikovComplex]
  rw [CochainComplex.of_d]
  exact coe_gradedNovikovMap_apply hδ rfl x

variable (R hF d hd δ hδ hδδ) in
/-- The basis of the term of degree `a` of the Novikov complex given by chosen lifts of the orbits
of degree `a`. -/
def novikovComplexBasis (r : ∀ i, P i) (a : A) :
    Module.Basis {i // orbitDegree d i = a} (NovikovSeries R H N)
      ((novikovComplex R hF d hd δ hδ hδδ).X a) :=
  (novikovGradeByBasis hF hd r a).map (novikovComplexXEquiv R hF d hd δ hδ hδδ a).symm

/-- The basis vector of an orbit is the basis vector of the completed module given by its chosen
lift. -/
@[simp]
theorem coe_novikovComplexXEquiv_novikovComplexBasis (r : ∀ i, P i) (a : A)
    (i : {i // orbitDegree d i = a}) :
    (novikovComplexXEquiv R hF d hd δ hδ hδδ a (novikovComplexBasis R hF d hd δ hδ hδδ r a i) :
      NovikovModule R F) = basis hF r i := by
  simp [novikovComplexBasis]

/-- The terms of the Novikov complex are free over the Novikov ring. -/
instance (a : A) :
    Module.Free (NovikovSeries R H N) ((novikovComplex R hF d hd δ hδ hδδ).X a) :=
  .of_basis (novikovComplexBasis R hF d hd δ hδ hδδ (fun _ => Classical.arbitrary _) a)

/-- The terms of the Novikov complex are finitely generated over the Novikov ring. -/
instance (a : A) :
    Module.Finite (NovikovSeries R H N) ((novikovComplex R hF d hd δ hδ hδδ).X a) :=
  .of_basis (novikovComplexBasis R hF d hd δ hδ hδδ (fun _ => Classical.arbitrary _) a)

end Complex

section HomotopyEquiv

universe u v w

variable {R : Type u} [Ring R] {H A : Type*} [AddGroup H] {N : H →+ ℝ} [AddGroup A] [One A]
  [DecidableEq A] {ι₁ ι₀ : Type v} [Finite ι₁] [Finite ι₀] {P₁ : ι₁ → Type w}
  {P₀ : ι₀ → Type w} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h}
  {hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h}
  {d₁ : (Σ i, P₁ i) → A} {hd₁ : ∀ i (g : H) (p : P₁ i), d₁ ⟨i, g +ᵥ p⟩ = d₁ ⟨i, p⟩}
  {δ₁ : (Σ i, P₁ i) → (Σ i, P₁ i) → R} {hδ₁ : IsLaurentKernel d₁ d₁ 1 δ₁}
  {hδδ₁ : ∀ p q, kernelComp δ₁ δ₁ p q = 0} {d₀ : (Σ k, P₀ k) → A}
  {hd₀ : ∀ k (g : H) (q : P₀ k), d₀ ⟨k, g +ᵥ q⟩ = d₀ ⟨k, q⟩}
  {δ₀ : (Σ k, P₀ k) → (Σ k, P₀ k) → R} {hδ₀ : IsLaurentKernel d₀ d₀ 1 δ₀}
  {hδδ₀ : ∀ p q, kernelComp δ₀ δ₀ p q = 0}

/-- The map of a Laurent kernel of degree `c` from the term of degree `a` to the term of degree
`b = a + c`, typed between the terms of two Novikov complexes so that it composes with their
differentials. -/
private def novikovComplexComponent {c : A} (m : (Σ i, P₁ i) → (Σ k, P₀ k) → R)
    (hm : IsLaurentKernel d₁ d₀ c m) {a b : A} (h : a + c = b) :
    (novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁).X a ⟶ (novikovComplex R hF₀ d₀ hd₀ δ₀ hδ₀ hδδ₀).X b :=
  ModuleCat.ofHom (gradedNovikovMap hF₁ hF₀ hd₁ hd₀ hm h)

private theorem coe_novikovComplexXEquiv_novikovComplexComponent_apply {c : A}
    (m : (Σ i, P₁ i) → (Σ k, P₀ k) → R) (hm : IsLaurentKernel d₁ d₀ c m) {a b : A}
    (h : a + c = b) (x : (novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁).X a) :
    (novikovComplexXEquiv R hF₀ d₀ hd₀ δ₀ hδ₀ hδδ₀ b
        ((novikovComplexComponent m hm h).hom x) : NovikovModule R F₀) =
      hm.novikovMap hF₁ hF₀
        (novikovComplexXEquiv R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ a x : NovikovModule R F₁) :=
  coe_gradedNovikovMap_apply hm h x

/-- The chain map of Novikov complexes given by a Laurent chain map `Φ` of degree `0`, one with
`δ₁ Φ = Φ δ₀` as composite kernels. Its components are the maps of `Φ` on the homogeneous pieces
(`TauCeti.NovikovModule.coe_novikovComplexXEquiv_novikovComplexHom_f_apply`). -/
def novikovComplexHom (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R) (hΦ : IsLaurentKernel d₁ d₀ 0 Φ)
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q) :
    novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ ⟶ novikovComplex R hF₀ d₀ hd₀ δ₀ hδ₀ hδδ₀ :=
  CochainComplex.ofHom (fun a => novikovComplexComponent Φ hΦ (add_zero a)) fun a => by
    ext x : 2
    refine (novikovComplexXEquiv R hF₀ d₀ hd₀ δ₀ hδ₀ hδδ₀ _).injective (Subtype.ext ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, coe_novikovComplexXEquiv_d_apply rfl,
      coe_novikovComplexXEquiv_novikovComplexComponent_apply]
    ext q
    rw [hΦ.novikovMap_novikovMap_apply_val hF₁ hF₀ hF₀ hδ₀,
      hδ₁.novikovMap_novikovMap_apply_val hF₁ hF₁ hF₀ hΦ]
    simp only [hΦδ]

/-- The components of the chain map of a Laurent chain map are its maps on the homogeneous
pieces. -/
@[simp]
theorem coe_novikovComplexXEquiv_novikovComplexHom_f_apply (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R)
    (hΦ : IsLaurentKernel d₁ d₀ 0 Φ) (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (a : A) (x : (novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁).X a) :
    (novikovComplexXEquiv R hF₀ d₀ hd₀ δ₀ hδ₀ hδδ₀ a (((novikovComplexHom Φ hΦ hΦδ).f a).hom x) :
      NovikovModule R F₀) =
        hΦ.novikovMap hF₁ hF₀
          (novikovComplexXEquiv R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ a x : NovikovModule R F₁) :=
  coe_novikovComplexXEquiv_novikovComplexComponent_apply Φ hΦ (add_zero a) x

variable [DecidableEq (Σ i, P₁ i)]

/-- Laurent chain maps `Φ` and `Ψ` with `Φ Ψ - 1 = K δ₁ + δ₁ K` for a Laurent kernel `K` of
degree `-1` give a homotopy between the composite of their chain maps and the identity. Its
component from degree `a` to degree `a - 1` is the map of `K`
(`TauCeti.NovikovModule.coe_novikovComplexXEquiv_novikovComplexHomotopy_hom_apply`). -/
def novikovComplexHomotopy (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R)
    (Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R) (K : (Σ i, P₁ i) → (Σ i, P₁ i) → R)
    (hΦ : IsLaurentKernel d₁ d₀ 0 Φ) (hΨ : IsLaurentKernel d₀ d₁ 0 Ψ)
    (hK : IsLaurentKernel d₁ d₁ (-1) K)
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q) :
    Homotopy (novikovComplexHom (hF₀ := hF₀) (hd₀ := hd₀) (hδ₀ := hδ₀) (hδδ₀ := hδδ₀) Φ hΦ hΦδ ≫
        novikovComplexHom Ψ hΨ hΨδ :
        novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ ⟶ novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁)
      (𝟙 (novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁)) where
  hom a b := if h : a + -1 = b then novikovComplexComponent K hK h else 0
  zero a b hab :=
    dite_eq_right fun h => hab (by rw [ComplexShape.up_Rel, ← h, neg_add_cancel_right])
  comm a := by
    rw [dNext_eq _ (show (ComplexShape.up A).Rel a (a + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up A).Rel (a - 1) a from sub_add_cancel a 1),
      dite_eq_left (add_neg_cancel_right a 1), dite_eq_left (sub_eq_add_neg a 1).symm]
    ext x : 2
    refine (novikovComplexXEquiv R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ a).injective (Subtype.ext ?_)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_add,
      ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_add, Submodule.coe_add,
      coe_novikovComplexXEquiv_novikovComplexHom_f_apply,
      coe_novikovComplexXEquiv_d_apply (show a + 1 = a + 1 from rfl),
      coe_novikovComplexXEquiv_d_apply (sub_add_cancel a 1),
      coe_novikovComplexXEquiv_novikovComplexComponent_apply K hK (sub_eq_add_neg a 1).symm,
      coe_novikovComplexXEquiv_novikovComplexComponent_apply K hK (add_neg_cancel_right a 1)]
    rw [← sub_eq_iff_eq_add, add_comm]
    exact hΦ.novikovMap_novikovMap_sub_eq hF₁ hF₀ hΨ hK hδ₁ hΦΨ _

/-- The component from degree `a` to degree `a - 1` of the homotopy given by a Laurent homotopy
`K` is the map of `K` on the homogeneous pieces. -/
@[simp]
theorem coe_novikovComplexXEquiv_novikovComplexHomotopy_hom_apply
    (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R) (Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R)
    (K : (Σ i, P₁ i) → (Σ i, P₁ i) → R) (hΦ : IsLaurentKernel d₁ d₀ 0 Φ)
    (hΨ : IsLaurentKernel d₀ d₁ 0 Ψ) (hK : IsLaurentKernel d₁ d₁ (-1) K)
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q) {a b : A} (h : a + -1 = b)
    (x : (novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁).X a) :
    (novikovComplexXEquiv R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ b
        (((novikovComplexHomotopy (hF₀ := hF₀) (hd₀ := hd₀) (hδ₀ := hδ₀) (hδδ₀ := hδδ₀) Φ Ψ K hΦ
          hΨ hK hΦδ hΨδ hΦΨ).hom a b).hom x) : NovikovModule R F₁) =
      hK.novikovMap hF₁ hF₁
        (novikovComplexXEquiv R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁ a x : NovikovModule R F₁) := by
  simp only [novikovComplexHomotopy, dite_eq_left h,
    coe_novikovComplexXEquiv_novikovComplexComponent_apply]

/-- The components of the homotopy given by a Laurent homotopy vanish outside degree `-1`. -/
theorem novikovComplexHomotopy_hom_of_add_ne (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R)
    (Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R) (K : (Σ i, P₁ i) → (Σ i, P₁ i) → R)
    (hΦ : IsLaurentKernel d₁ d₀ 0 Φ) (hΨ : IsLaurentKernel d₀ d₁ 0 Ψ)
    (hK : IsLaurentKernel d₁ d₁ (-1) K)
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q) {a b : A} (h : a + -1 ≠ b) :
    (novikovComplexHomotopy (hF₁ := hF₁) (hd₁ := hd₁) (hδ₁ := hδ₁) (hδδ₁ := hδδ₁) (hF₀ := hF₀)
      (hd₀ := hd₀) (hδ₀ := hδ₀) (hδδ₀ := hδδ₀) Φ Ψ K hΦ hΨ hK hΦδ hΨδ hΦΨ).hom a b = 0 :=
  dite_eq_right h

variable [DecidableEq (Σ k, P₀ k)]

/-- **The homotopy equivalence of Novikov complexes.** Laurent chain maps `Φ` and `Ψ` of degree
`0` between Laurent differentials `δ₁` and `δ₀`, inverse to each other up to Laurent homotopies
`K` and `K'` of degree `-1`, give a homotopy equivalence between the Novikov complexes of `δ₁`
and `δ₀`. Its maps are the chain maps of `Φ` and `Ψ`
(`TauCeti.NovikovModule.novikovComplexHom`). The same data specialize on the finite Laurent
model to a homotopy equivalence of cyclic complexes,
`TauCeti.NovikovModule.cyclicComplexHomotopyEquiv`. -/
@[expose, simps hom inv homotopyHomInvId homotopyInvHomId]
def novikovComplexHomotopyEquiv (Φ : (Σ i, P₁ i) → (Σ k, P₀ k) → R)
    (Ψ : (Σ k, P₀ k) → (Σ i, P₁ i) → R) (K : (Σ i, P₁ i) → (Σ i, P₁ i) → R)
    (K' : (Σ k, P₀ k) → (Σ k, P₀ k) → R) (hΦ : IsLaurentKernel d₁ d₀ 0 Φ)
    (hΨ : IsLaurentKernel d₀ d₁ 0 Ψ) (hK : IsLaurentKernel d₁ d₁ (-1) K)
    (hK' : IsLaurentKernel d₀ d₀ (-1) K')
    (hΦδ : ∀ p q, kernelComp δ₁ Φ p q = kernelComp Φ δ₀ p q)
    (hΨδ : ∀ p q, kernelComp δ₀ Ψ p q = kernelComp Ψ δ₁ p q)
    (hΦΨ : ∀ p q, kernelComp Φ Ψ p q - (if p = q then 1 else 0) =
      kernelComp K δ₁ p q + kernelComp δ₁ K p q)
    (hΨΦ : ∀ p q, kernelComp Ψ Φ p q - (if p = q then 1 else 0) =
      kernelComp K' δ₀ p q + kernelComp δ₀ K' p q) :
    HomotopyEquiv (novikovComplex R hF₁ d₁ hd₁ δ₁ hδ₁ hδδ₁)
      (novikovComplex R hF₀ d₀ hd₀ δ₀ hδ₀ hδδ₀) where
  hom := novikovComplexHom Φ hΦ hΦδ
  inv := novikovComplexHom Ψ hΨ hΨδ
  homotopyHomInvId := novikovComplexHomotopy Φ Ψ K hΦ hΨ hK hΦδ hΨδ hΦΨ
  homotopyInvHomId := novikovComplexHomotopy Ψ Φ K' hΨ hΦ hK' hΨδ hΦδ hΨΦ

end HomotopyEquiv

end NovikovModule

end TauCeti
