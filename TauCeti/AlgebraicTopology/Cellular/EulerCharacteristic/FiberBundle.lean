/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import TauCeti.AlgebraicTopology.Singular.Fibration.Finrank
import TauCeti.Topology.CWComplex.Comparison

/-!
# Multiplicativity of the Euler characteristic for Serre fibrations and fibre bundles

Let `p : E ⟶ B` be a Serre fibration over a space `B` of finite CW type. Choosing a homotopy
equivalence `B ≃ₕ Z` with a Hausdorff space `Z` carrying a finite CW structure on `univ`
(`TauCeti.FiniteCWType.exists_homotopyEquiv_univ`), the base change of `p` along the inverse `Z → B`
is a Serre fibration over the finite CW complex `Z` whose projection to `E` is a weak homotopy
equivalence (`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`) and whose fibres are
homeomorphic to the corresponding fibres of `p`. Filtering that pullback by the preimages of the
skeleta of `Z` (`TauCeti.TopCat.finsum_finrank_singularHomology_of_isWeakHomotopyEquivalence_of_eq`)
transfers homological finiteness, eventual vanishing, and Euler's equality from the fibres to `E`,
with no connectedness or paracompactness assumption on `B` and no hypothesis on the monodromy:

* over a Noetherian ring `k`, `Hᵢ(E; k)` is finitely generated whenever `H_q(p⁻¹(b); k)` is
  finitely generated for every `b : B` and `q ≤ i`
  (`TauCeti.TopCat.finite_singularHomology_of_mem_serreFibrations`);
* over any ring `k`, `Hᵢ(E; k)` vanishes for all sufficiently large `i` whenever each fibre has
  eventually vanishing homology
  (`TauCeti.TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations`);
* over a division ring `k`, if every fibre of `p` has finite-dimensional, eventually vanishing
  homology with alternating dimension sum `c`, then
  `∑ᶠ i, (-1)ⁱ dim Hᵢ(E; k) = eulerChar B · c`
  (`TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations`), and when `E` and every
  fibre also have finite CW type with fibre Euler characteristic `c`,
  `eulerChar E = eulerChar B · c` (`TauCeti.TopCat.eulerChar_of_mem_serreFibrations`).

Every map `p : E → B` covered by local trivializations with model fibre `F` is a Serre fibration
(`TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`) whose fibres are homeomorphic to `F`
(`Bundle.Trivialization.preimageSingletonHomeomorph`). Specializing to locally trivial maps and to
fibre bundles (`FiberBundle F E`) with `B` and `F` of finite CW type yields
`TauCeti.finsum_finrank_singularHomology_of_exists_trivialization`,
`TauCeti.finsum_finrank_singularHomology_fiberBundle`, and `TauCeti.eulerChar_fiberBundle`, without
assuming a finite CW model on the total space until `eulerChar` of the total space is formed.

## Main results

* `TauCeti.TopCat.finite_singularHomology_of_mem_serreFibrations`,
  `TauCeti.TopCat.finite_singularHomology_of_mem_serreFibrations_of_finiteCWType`: finite generation
  of `Hᵢ(E; k)` over a Noetherian ring for a Serre fibration over a base of finite CW type.
* `TauCeti.TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations`,
  `TauCeti.TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations_of_finiteCWType`:
  eventual vanishing of `Hᵢ(E; k)` for a Serre fibration over a base of finite CW type.
* `TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations`,
  `TauCeti.TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations_of_finiteCWType`,
  `TauCeti.TopCat.eulerChar_of_mem_serreFibrations`: multiplicativity of the alternating homology
  dimension sum and of `eulerChar` for Serre fibrations over a base of finite CW type.
* `TauCeti.finite_singularHomology_of_exists_trivialization`,
  `TauCeti.eventually_isZero_singularHomology_of_exists_trivialization`,
  `TauCeti.finsum_finrank_singularHomology_of_exists_trivialization`,
  `TauCeti.eulerChar_of_exists_trivialization`: the corresponding statements for locally trivial
  maps with model fibre `F` of finite CW type.
* `TauCeti.finite_singularHomology_fiberBundle`,
  `TauCeti.eventually_isZero_singularHomology_fiberBundle`,
  `TauCeti.finsum_finrank_singularHomology_fiberBundle`, `TauCeti.eulerChar_fiberBundle`:
  finiteness, eventual vanishing, and multiplicativity `χ(E) = χ(B) · χ(F)` for fibre bundles whose
  base and fibre have finite CW type.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II, Proposition 7.
* E. H. Spanier, *Algebraic Topology*, Chapter 9, Section 3, Theorem 1, p. 481.
* J. R. Klein, C. Malkiewich, M. Ramzi, *On the multiplicativity of the Euler characteristic*,
  pp. 1–2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

section SerreFibration

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) [FiniteCWType B]

include hp

/-- **Finiteness of total-space homology for a Serre fibration.** Let `p : E ⟶ B` be a Serre
fibration over a base `B` of finite CW type. Over a Noetherian ring `k`, if `H_q(p⁻¹(b); k)` is
finitely generated for every `b : B` and `q ≤ i`, then `Hᵢ(E; k)` is finitely generated. -/
theorem finite_singularHomology_of_mem_serreFibrations (k : Type u) [Ring k] [IsNoetherianRing k]
    (i : ℕ) (hfib : ∀ b, ∀ q ≤ i, Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b))) :
    Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) := by
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  exact finite_singularHomology_of_isWeakHomotopyEquivalence hp k
    (g := _root_.TopCat.ofHom e.symm.toFun) e.symm.isWeakHomotopyEquivalence i
    (fun m _ ↦ FiniteType.finite_cell m) fun m _ _ ↦ hfib _ (i - m) (Nat.sub_le i m)

/-- Over a Noetherian ring `k`, if `p : E ⟶ B` is a Serre fibration whose base and fibres all have
finite CW type, then `Hᵢ(E; k)` is finitely generated in every degree `i`. -/
theorem finite_singularHomology_of_mem_serreFibrations_of_finiteCWType (k : Type u) [Ring k]
    [IsNoetherianRing k] [∀ b, FiniteCWType (p.fiber b)] (i : ℕ) :
    Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) :=
  finite_singularHomology_of_mem_serreFibrations hp k i fun b q _ ↦
    finite_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k) q

/-- **Eventual vanishing of total-space homology for a Serre fibration.** Let `p : E ⟶ B` be a Serre
fibration over a base `B` of finite CW type. Over any ring `k`, if `H_q(p⁻¹(b); k)` vanishes for
all sufficiently large `q` at every point `b : B`, then `Hᵢ(E; k)` vanishes for all sufficiently
large `i`. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations (k : Type u) [Ring k]
    (hzero : ∀ b, ∀ᶠ q in Filter.atTop, Limits.IsZero
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b))) :
    ∀ᶠ i in Filter.atTop, Limits.IsZero
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) := by
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  exact eventually_isZero_singularHomology_of_isWeakHomotopyEquivalence hp k
    (g := _root_.TopCat.ofHom e.symm.toFun) e.symm.isWeakHomotopyEquivalence fun _ _ ↦ hzero _

/-- Over any ring `k`, if `p : E ⟶ B` is a Serre fibration whose base and fibres all have finite CW
type, then `Hᵢ(E; k)` vanishes for all sufficiently large `i`. -/
theorem eventually_isZero_singularHomology_of_mem_serreFibrations_of_finiteCWType (k : Type u)
    [Ring k] [∀ b, FiniteCWType (p.fiber b)] :
    ∀ᶠ i in Filter.atTop, Limits.IsZero
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) :=
  eventually_isZero_singularHomology_of_mem_serreFibrations hp k fun b ↦
    eventually_isZero_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k)

/-- **Multiplicativity of the Euler characteristic for a Serre fibration.** Let `p : E ⟶ B` be a
Serre fibration over a base `B` of finite CW type. Over a division ring `k`, if every fibre of `p`
has finite-dimensional, eventually vanishing singular homology with alternating dimension sum `c`,
then the alternating dimension sum of `Hᵢ(E; k)` is `eulerChar B · c`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations (k : Type u) [DivisionRing k]
    {c : ℤ}
    (hfin : ∀ b q, Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)))
    (hzero : ∀ b, ∀ᶠ q in Filter.atTop, Limits.IsZero
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj (p.fiber b)))
    (hc : ∀ b, ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (ModuleCat.of k k)).obj
        (p.fiber b)) : ℤ) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) : ℤ) =
      eulerChar B * c := by
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  rw [eulerChar_eq_cwEulerChar (e.trans (Homeomorph.Set.univ Z).symm.toHomotopyEquiv)]
  exact finsum_finrank_singularHomology_of_isWeakHomotopyEquivalence_of_eq hp k
    (g := _root_.TopCat.ofHom e.symm.toFun) e.symm.isWeakHomotopyEquivalence
    (fun _ _ q ↦ hfin _ q) (fun _ _ ↦ hzero _) fun _ _ ↦ hc _

/-- Over a division ring `k`, if `p : E ⟶ B` is a Serre fibration whose base and fibres all have
finite CW type and every fibre has Euler characteristic `c`, then the alternating dimension sum of
`Hᵢ(E; k)` is `eulerChar B · c`. -/
theorem finsum_finrank_singularHomology_of_mem_serreFibrations_of_finiteCWType (k : Type u)
    [DivisionRing k] [∀ b, FiniteCWType (p.fiber b)] {c : ℤ}
    (hc : ∀ b, eulerChar (p.fiber b) = c) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
        (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj E) : ℤ) =
      eulerChar B * c :=
  finsum_finrank_singularHomology_of_mem_serreFibrations hp k
    (fun b q ↦ finite_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k) q)
    (fun b ↦ eventually_isZero_singularHomology_of_finiteCWType (p.fiber b) (ModuleCat.of k k))
    fun b ↦ (eulerChar_eq_finsum_finrank_singularHomology (p.fiber b) k).symm.trans (hc b)

/-- **Multiplicativity of `eulerChar` for a Serre fibration.** If `p : E ⟶ B` is a Serre fibration
whose total space, base, and fibres all have finite CW type, and every fibre has Euler
characteristic `c`, then `eulerChar E = eulerChar B · c`. -/
theorem eulerChar_of_mem_serreFibrations [FiniteCWType E] [∀ b, FiniteCWType (p.fiber b)]
    {c : ℤ} (hc : ∀ b, eulerChar (p.fiber b) = c) :
    eulerChar E = eulerChar B * c := by
  rw [eulerChar_eq_finsum_finrank_singularHomology E (ULift.{u} ℚ)]
  exact finsum_finrank_singularHomology_of_mem_serreFibrations_of_finiteCWType hp (ULift.{u} ℚ) hc

end SerreFibration

end TopCat

section Trivialization

variable {E B F : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
  {p : E → B}

/-- A locally trivial map `p : E → B` packaged as a morphism in `TopCat`. -/
private def trivializationHom (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) :
    TopCat.of E ⟶ TopCat.of B :=
  TopCat.ofHom ⟨p, continuous_of_forall_exists_trivialization h⟩

/-- Each fibre of a locally trivial map with model fibre `F` of finite CW type has finite CW
type. -/
private theorem finiteCWType_fiber_trivializationHom
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) [FiniteCWType F]
    (b : TopCat.of B) : FiniteCWType ((trivializationHom h).fiber b) := by
  obtain ⟨e, hb⟩ := h b
  exact (e.preimageSingletonHomeomorph hb).finiteCWType

/-- Each fibre of a locally trivial map with model fibre `F` of finite CW type has Euler
characteristic `eulerChar F`. -/
private theorem eulerChar_fiber_trivializationHom
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) [FiniteCWType F]
    (b : TopCat.of B) :
    haveI := finiteCWType_fiber_trivializationHom h b
    eulerChar ((trivializationHom h).fiber b) = eulerChar F := by
  obtain ⟨e, hb⟩ := h b
  have : FiniteCWType ↑(p ⁻¹' {b}) := (e.preimageSingletonHomeomorph hb).finiteCWType
  exact (e.preimageSingletonHomeomorph hb).eulerChar_eq

/-- Over a Noetherian ring `k`, the total space of a locally trivial map whose base `B` and model
fibre `F` have finite CW type has finitely generated singular homology in every degree. -/
theorem finite_singularHomology_of_exists_trivialization (k : Type u) [Ring k] [IsNoetherianRing k]
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) [FiniteCWType B] [FiniteCWType F]
    (i : ℕ) :
    Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of E)) := by
  have := finiteCWType_fiber_trivializationHom h
  exact TopCat.finite_singularHomology_of_mem_serreFibrations_of_finiteCWType
    (TopCat.mem_serreFibrations_of_exists_trivialization (p := trivializationHom h) h) k i

/-- Over any ring `k`, the singular homology of the total space of a locally trivial map whose base
`B` and model fibre `F` have finite CW type vanishes in all sufficiently large degrees. -/
theorem eventually_isZero_singularHomology_of_exists_trivialization (k : Type u) [Ring k]
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) [FiniteCWType B] [FiniteCWType F] :
    ∀ᶠ i in Filter.atTop, Limits.IsZero
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of E)) := by
  have := finiteCWType_fiber_trivializationHom h
  exact TopCat.eventually_isZero_singularHomology_of_mem_serreFibrations_of_finiteCWType
    (TopCat.mem_serreFibrations_of_exists_trivialization (p := trivializationHom h) h) k

/-- **Multiplicativity of the Euler characteristic for a locally trivial map.** Let `p : E → B` be
covered by local trivializations with model fibre `F`, where `B` and `F` have finite CW type. Over
any division ring `k`, the alternating sum of the dimensions of `Hᵢ(E; k)` is
`eulerChar B · eulerChar F`, with no hypothesis on the monodromy or on `FiniteCWType E`. -/
theorem finsum_finrank_singularHomology_of_exists_trivialization (k : Type u) [DivisionRing k]
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) [FiniteCWType B] [FiniteCWType F] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of E)) : ℤ) =
      eulerChar B * eulerChar F := by
  have := finiteCWType_fiber_trivializationHom h
  exact TopCat.finsum_finrank_singularHomology_of_mem_serreFibrations_of_finiteCWType
    (TopCat.mem_serreFibrations_of_exists_trivialization (p := trivializationHom h) h) k
    (eulerChar_fiber_trivializationHom h)

/-- **Multiplicativity of `eulerChar` for a locally trivial map.** If `p : E → B` is covered by
local trivializations with model fibre `F`, and `E`, `B`, and `F` all have finite CW type, then
`eulerChar E = eulerChar B · eulerChar F`. -/
theorem eulerChar_of_exists_trivialization
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) [FiniteCWType E] [FiniteCWType B]
    [FiniteCWType F] :
    eulerChar E = eulerChar B * eulerChar F := by
  rw [eulerChar_eq_finsum_finrank_singularHomology E (ULift.{u} ℚ)]
  exact finsum_finrank_singularHomology_of_exists_trivialization (ULift.{u} ℚ) h

end Trivialization

section FiberBundle

/-- Over a Noetherian ring `k`, the total space of a fibre bundle whose base `B` and fibre `F` have
finite CW type has finitely generated singular homology in every degree. -/
theorem finite_singularHomology_fiberBundle (k : Type u) [Ring k] [IsNoetherianRing k]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] (i : ℕ) :
    Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj
        (ModuleCat.of k k)).obj (TopCat.of (Bundle.TotalSpace F E))) :=
  finite_singularHomology_of_exists_trivialization k
    (FiberBundle.exists_trivialization_mem_baseSet F E) i

/-- Over any ring `k`, the singular homology of the total space of a fibre bundle whose base `B` and
fibre `F` have finite CW type vanishes in all sufficiently large degrees. -/
theorem eventually_isZero_singularHomology_fiberBundle (k : Type u) [Ring k]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∀ᶠ i in Filter.atTop, Limits.IsZero
      (((singularHomologyFunctor (ModuleCat.{u} k) i).obj
        (ModuleCat.of k k)).obj (TopCat.of (Bundle.TotalSpace F E))) :=
  eventually_isZero_singularHomology_of_exists_trivialization k
    (FiberBundle.exists_trivialization_mem_baseSet F E)

/-- **Multiplicativity of the Euler characteristic in fibre bundles.** For a fibre bundle `E` with
base `B` and model fibre `F` of finite CW type, the alternating sum of the dimensions of the
singular homology of the total space over any division ring `k` is `eulerChar B · eulerChar F`, with
no hypothesis on the monodromy and no finite CW model assumed on the total space. -/
theorem finsum_finrank_singularHomology_fiberBundle (k : Type u) [DivisionRing k]
    {B F : Type u} [TopologicalSpace B] [TopologicalSpace F] (E : B → Type u)
    [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [FiniteCWType B] [FiniteCWType F] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
        (ModuleCat.of k k)).obj (TopCat.of (Bundle.TotalSpace F E))) : ℤ) =
      eulerChar B * eulerChar F :=
  finsum_finrank_singularHomology_of_exists_trivialization k
    (FiberBundle.exists_trivialization_mem_baseSet F E)

/-- **Multiplicativity of `eulerChar` in fibre bundles.** If the base `B`, model fibre `F`, and
total space `Bundle.TotalSpace F E` of a fibre bundle all have finite CW type, then
`eulerChar (Bundle.TotalSpace F E) = eulerChar B · eulerChar F`. -/
theorem eulerChar_fiberBundle {B F : Type u} [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type u) [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [FiniteCWType B] [FiniteCWType F] [FiniteCWType (Bundle.TotalSpace F E)] :
    eulerChar (Bundle.TotalSpace F E) = eulerChar B * eulerChar F :=
  eulerChar_of_exists_trivialization (FiberBundle.exists_trivialization_mem_baseSet F E)

end FiberBundle

end TauCeti
