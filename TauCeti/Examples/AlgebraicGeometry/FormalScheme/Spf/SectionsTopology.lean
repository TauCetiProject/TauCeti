/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Examples and counterexamples for the topology on sections of `Spf A`

We verify the behaviour of `sectionsTopology` and `quotientSectionsTopology` on four test cases:

1. **Discrete ring (`I = ⊥`, quasi-compact open):** when `A` carries the discrete topology (adic
   for `⊥`), `quotientSectionsTopology` on any quasi-compact open `U` of `Spf A` is discrete (`⊥`).
2. **Empty open (`⊥`):** for any adic ring `(A, I)`, the section ring `Γ(⊥, O_{Spf A})` over the
   empty open is a subsingleton and carries the discrete topology.
3. **`p`-adic integers (`ℤ_[p]`, `I = (p)`):** the global sections isomorphism
   `Γ(⊤, O_{Spf ℤ_[p]}) ≅ ℤ_[p]` is a homeomorphism onto `ℤ_[p]` with its `(p)`-adic norm
   topology, which is complete, Hausdorff, and not discrete.
4. **Infinite product of a field (`A = ℕ → k` discrete, `I = ⊥`):** on the non-quasi-compact open
   `U = ⋃ n : ℕ, D(eₙ)` spanned by the coordinate idempotents `eₙ = Pi.single n 1`, each `D(eₙ)` is
   a singleton with section ring `k`, and `Γ(U, O_{Spf A})` equipped with
   `quotientSectionsTopology` is isomorphic as a topological ring to `∏ n : ℕ, k` with the product
   of discrete topologies. In particular, `quotientSectionsTopology` on `U` is not discrete, while
   `sectionsTopology` on `U` is `⊥`, so `sectionsTopology hI U < quotientSectionsTopology hI U`
   (Stacks Project, Tag 0AHY).

## References

* [Grothendieck, *Éléments de géométrie algébrique* I][ega1], Chapter 0, §3.8.1 and Chapter I,
  §10.1.1–10.1.4.
* [The Stacks Project Authors, *Stacks Project*][stacks-project], Tag 0AHY.
-/

public section

universe u

open CategoryTheory Function Opposite TopologicalSpace Topology IsLocalRing
open TauCeti.FormalScheme.Spf

namespace TauCeti

/-! ### 1. Discrete ring on a quasi-compact open -/

/-- For a discrete ring `A` with ideal of definition `⊥`, `quotientSectionsTopology` on any
quasi-compact open `U` of `Spf A` is `⊥` (hence discrete). -/
example (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (hI : IsAdic (⊥ : Ideal A)) (U : Opens (carrier A)) (hU : IsCompact (U : Set (carrier A))) :
    quotientSectionsTopology hI U = ⊥ ∧ @DiscreteTopology _ (quotientSectionsTopology hI U) := by
  have heq : quotientSectionsTopology hI U = ⊥ :=
    (quotientSectionsTopology_eq_of_isCompact hI hU).trans (sectionsTopology_bot_eq_bot hI U)
  exact ⟨heq, heq ▸ discreteTopology_bot _⟩

/-- Concrete instantiation on `ℤ` with the discrete topology and `U = ⊤`. -/
example :
    letI : TopologicalSpace ℤ := ⊥
    haveI : DiscreteTopology ℤ := discreteTopology_bot ℤ
    ∃ hI : IsAdic (⊥ : Ideal ℤ),
      quotientSectionsTopology hI ⊤ = ⊥ ∧ @DiscreteTopology _ (quotientSectionsTopology hI ⊤) := by
  let _ : TopologicalSpace ℤ := ⊥
  have : DiscreteTopology ℤ := discreteTopology_bot ℤ
  have hI : IsAdic (⊥ : Ideal ℤ) := isAdic_iff.mpr
    ⟨fun _ ↦ isOpen_discrete _, fun s hs ↦
      ⟨1, by simpa [pow_one] using Set.singleton_subset_iff.mpr (mem_of_mem_nhds hs)⟩⟩
  have heq : quotientSectionsTopology hI ⊤ = ⊥ :=
    (quotientSectionsTopology_top hI).trans (sectionsTopology_bot_eq_bot hI ⊤)
  exact ⟨hI, heq, heq ▸ discreteTopology_bot _⟩

/-! ### 2. Empty open -/

/-- Over the empty open `⊥` of `Spf A`, the section ring is trivial and carries the discrete
topology. -/
example (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {I : Ideal A}
    (hI : IsAdic I) :
    Subsingleton ((structureSheaf hI).obj.obj (op (⊥ : Opens (carrier A)))) ∧
      quotientSectionsTopology hI (⊥ : Opens (carrier A)) = ⊥ ∧
      @DiscreteTopology _ (quotientSectionsTopology hI (⊥ : Opens (carrier A))) := by
  let _ := quotientSectionsTopology hI (⊥ : Opens (carrier A))
  exact ⟨inferInstance, quotientSectionsTopology_bot hI, inferInstance⟩

/-! ### 3. `p`-adic integers `ℤ_[p]` -/

/-- For `A = ℤ_[p]` with `I = (p)`, the global sections isomorphism `Γ(⊤, O_{Spf ℤ_[p]}) ≅ ℤ_[p]`
is a homeomorphism onto `ℤ_[p]`, and `quotientSectionsTopology` on `⊤` is a complete Hausdorff
topological ring topology that is not discrete. -/
example (p : ℕ) [Fact p.Prime] :
    let hI := Huber.PadicInt.isAdic_maximalIdeal (p := p)
    letI := quotientSectionsTopology hI ⊤
    haveI := quotientSectionsTopology_isTopologicalRing hI ⊤
    letI : UniformSpace ((structureSheaf hI).obj.obj (op ⊤)) :=
      IsTopologicalAddGroup.rightUniformSpace _
    IsHomeomorph ((globalSectionsIso hI).hom) ∧
      CompleteSpace ((structureSheaf hI).obj.obj (op ⊤)) ∧
      T2Space ((structureSheaf hI).obj.obj (op ⊤)) ∧
      ¬ DiscreteTopology ((structureSheaf hI).obj.obj (op ⊤)) := by
  let hI := Huber.PadicInt.isAdic_maximalIdeal (p := p)
  let _ := quotientSectionsTopology hI ⊤
  have := quotientSectionsTopology_isTopologicalRing hI ⊤
  let _ : UniformSpace ((structureSheaf hI).obj.obj (op ⊤)) :=
    IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup ((structureSheaf hI).obj.obj (op ⊤)) :=
    isUniformAddGroup_of_addCommGroup
  have hhomeo := isHomeomorph_globalSectionsIso hI
  refine ⟨hhomeo, quotientSectionsTopology_completeSpace hI ⊤ rfl,
    quotientSectionsTopology_t2Space hI ⊤, fun hdisc ↦ ?_⟩
  have hdiscZ : DiscreteTopology ℤ_[p] := hhomeo.homeomorph.discreteTopology_iff.mp hdisc
  have hnil : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (𝓝 0) :=
    (Huber.PadicInt.isTopologicallyNilpotent_iff_dvd (c := (p : ℤ_[p]))).mpr dvd_rfl
  rw [nhds_discrete, Filter.tendsto_pure] at hnil
  obtain ⟨n, hn⟩ := hnil.exists
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hn

/-! ### 4. Infinite product of a field `ℕ → k` (Stacks Project, Tag 0AHY) -/

/-- The product of countably many copies of a field `k`, each with the discrete topology, is not
discrete. -/
private theorem not_discreteTopology_pi_bot (k : Type u) [Field k] :
    ¬ @DiscreteTopology (ℕ → k) (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥) := by
  classical
  let _ : TopologicalSpace k := ⊥
  have : DiscreteTopology k := discreteTopology_bot k
  intro hdisc
  have htend : Filter.Tendsto (fun m : ℕ ↦ Pi.single m (1 : k)) Filter.atTop (𝓝 0) := by
    refine tendsto_pi_nhds.mpr fun i ↦ ?_
    rw [nhds_discrete, Filter.tendsto_pure]
    exact (Filter.eventually_ge_atTop (i + 1)).mono fun m hm ↦ by
      simp [Pi.single_eq_of_ne (Nat.ne_of_lt hm)]
  rw [nhds_discrete, Filter.tendsto_pure] at htend
  obtain ⟨m, hm⟩ := htend.exists
  have h10 : (1 : k) = 0 := by simpa using congrFun hm m
  exact one_ne_zero h10

namespace SpfInfiniteProductChecks

variable (k : Type u) [Field k]

/-- Equip the infinite product `ℕ → k` with the discrete topology for the counterexample. -/
local instance discreteTopologicalSpacePi : TopologicalSpace (ℕ → k) := ⊥

local instance discreteTopologyPi : DiscreteTopology (ℕ → k) := ⟨rfl⟩

/-- Coordinate idempotent `eₙ = Pi.single n 1` in `ℕ → k`. -/
private noncomputable abbrev coordIdem (n : ℕ) : ℕ → k :=
  by classical exact Pi.single n 1

private theorem coordIdem_mul_of_ne {n m : ℕ} (hnm : n ≠ m) :
    coordIdem k n * coordIdem k m = 0 := by
  classical
  ext i
  rw [Pi.mul_apply, Pi.zero_apply, coordIdem, coordIdem]
  by_cases hi : i = n
  · subst hi
    rw [Pi.single_eq_of_ne hnm, mul_zero]
  · rw [Pi.single_eq_of_ne hi, zero_mul]

private theorem isAdic_bot_pi : IsAdic (⊥ : Ideal (ℕ → k)) :=
  isAdic_iff.mpr ⟨fun _ ↦ isOpen_discrete _, fun s hs ↦
    ⟨1, by simpa [pow_one] using Set.singleton_subset_iff.mpr (mem_of_mem_nhds hs)⟩⟩

/-- The `n`-th coordinate kernel `ker (eval n)` as an open prime point of `Spf (ℕ → k)`. -/
private noncomputable def coordPoint (n : ℕ) : carrier (ℕ → k) :=
  have hmax : (RingHom.ker (Pi.evalRingHom (fun _ : ℕ ↦ k) n)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (Pi.evalRingHom (fun _ : ℕ ↦ k) n).surjective
  ⟨⟨RingHom.ker (Pi.evalRingHom (fun _ : ℕ ↦ k) n), hmax.isPrime⟩,
    mem_carrier.mpr (isOpen_discrete _)⟩

private theorem coordPoint_mem_basicOpen (n : ℕ) :
    coordPoint k n ∈ basicOpen (coordIdem k n) := by
  classical
  rw [mem_basicOpen, coordPoint, RingHom.mem_ker, coordIdem]
  simp

private theorem disjoint_basicOpen_coordIdem :
    Pairwise (Disjoint on fun n : ℕ ↦ basicOpen (coordIdem k n)) := by
  intro n m hnm
  rw [Function.onFun_apply, disjoint_iff, ← basicOpen_mul, coordIdem_mul_of_ne k hnm,
    basicOpen_zero]

/-- Each basic open `D(eₙ)` in `Spf (ℕ → k)` is a singleton consisting of `coordPoint k n`. -/
@[instance_reducible]
private noncomputable def uniqueBasicOpenCoordIdem (n : ℕ) :
    Unique (basicOpen (coordIdem k n)) := by
  classical
  refine ⟨⟨⟨coordPoint k n, coordPoint_mem_basicOpen k n⟩⟩, fun q ↦ ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply PrimeSpectrum.ext
  have hmax : (RingHom.ker (Pi.evalRingHom (fun _ : ℕ ↦ k) n)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (Pi.evalRingHom (fun _ : ℕ ↦ k) n).surjective
  refine (hmax.eq_of_le q.1.1.isPrime.ne_top fun x hx ↦ ?_).symm
  have hx0 : x * coordIdem k n = 0 := by
    ext j
    rw [Pi.mul_apply, Pi.zero_apply, coordIdem]
    by_cases hj : j = n
    · subst hj
      have hxn : x j = 0 := hx
      simp [hxn]
    · rw [Pi.single_eq_of_ne hj, mul_zero]
  have hmem : x * coordIdem k n ∈ q.1.1.asIdeal := hx0 ▸ q.1.1.asIdeal.zero_mem
  exact (q.1.1.isPrime.mem_or_mem hmem).resolve_right (mem_basicOpen.mp q.2)

/-- The union `U = ⋃ n : ℕ, D(eₙ)` in `Spf (ℕ → k)` is not quasi-compact. -/
private theorem not_isCompact_iSup_basicOpen_coordIdem :
    ¬ IsCompact (((⨆ n : ℕ, basicOpen (coordIdem k n) : Opens (carrier (ℕ → k))) :
      Set (carrier (ℕ → k)))) := by
  intro hcomp
  have hcov : (((⨆ n : ℕ, basicOpen (coordIdem k n) : Opens (carrier (ℕ → k))) :
      Set (carrier (ℕ → k)))) ⊆ ⋃ n : ℕ, (basicOpen (coordIdem k n) : Set _) := by
    simp
  obtain ⟨s, hs⟩ := hcomp.elim_finite_subcover
    (fun n : ℕ ↦ (basicOpen (coordIdem k n) : Set _))
    (fun n ↦ (basicOpen (coordIdem k n)).isOpen) hcov
  let m : ℕ := s.sup id + 1
  have hmU : coordPoint k m ∈ (⨆ n : ℕ, basicOpen (coordIdem k n) : Opens (carrier (ℕ → k))) :=
    Opens.mem_iSup.mpr ⟨m, coordPoint_mem_basicOpen k m⟩
  obtain ⟨i, his, hmi⟩ := Set.mem_iUnion₂.mp (hs hmU)
  have hne : m ≠ i := Nat.ne_of_gt (Nat.lt_succ_of_le (Finset.le_sup (f := id) his))
  have hbot : basicOpen (coordIdem k m) ⊓ basicOpen (coordIdem k i) = ⊥ :=
    (disjoint_basicOpen_coordIdem k hne).eq_bot
  have hmem : coordPoint k m ∈ (basicOpen (coordIdem k m) ⊓ basicOpen (coordIdem k i) : Opens _) :=
    ⟨coordPoint_mem_basicOpen k m, hmi⟩
  rw [hbot] at hmem
  exact hmem

/-- Over `D(eₙ)`, the section ring `Γ(D(eₙ), O_{Spf (ℕ → k)})` is isomorphic to `k`. -/
private noncomputable def basicOpenCoordIdemRingEquiv (n : ℕ) :
    ((structureSheaf (isAdic_bot_pi k)).obj.obj (op (basicOpen (coordIdem k n)))) ≃+* k := by
  classical
  let hI := isAdic_bot_pi k
  let _ : Algebra (ℕ → k) k := (Pi.evalRingHom (fun _ : ℕ ↦ k) n).toAlgebra
  have hloc : IsLocalization.Away (coordIdem k n) k := by
    apply IsLocalization.away_of_isIdempotentElem
    · simp [coordIdem, IsIdempotentElem, ← Pi.single_mul_left]
    · exact RingHom.ker_evalRingHom (fun _ : ℕ ↦ k) n
    · exact (Pi.evalRingHom (fun _ : ℕ ↦ k) n).surjective
  let J : Ideal (Localization.Away (coordIdem k n)) :=
    (⊥ : Ideal (ℕ → k)).map (algebraMap (ℕ → k) (Localization.Away (coordIdem k n)))
  have : IsAdicComplete J (Localization.Away (coordIdem k n)) := by
    dsimp [J]
    rw [Ideal.map_bot]
    infer_instance
  exact (basicOpenSectionsAdicCompletionIso hI (coordIdem k n)).commRingCatIsoToRingEquiv.trans <|
    (AdicCompletion.ofAlgEquiv J).symm.toRingEquiv.trans <|
      (IsLocalization.algEquiv (.powers (coordIdem k n))
        (Localization.Away (coordIdem k n)) k).toRingEquiv

/-- On `U = ⋃ n : ℕ, D(eₙ)`, the product of restrictions
`Γ(U, O_{Spf (ℕ → k)}) → ∏ n, Γ(D(eₙ), O_{Spf (ℕ → k)})` is surjective because the `D(eₙ)` are
pairwise disjoint. -/
private theorem surjective_restrict_pi_coordIdem :
    Function.Surjective
      (fun (s : (structureSheaf (isAdic_bot_pi k)).obj.obj
          (op (⨆ n : ℕ, basicOpen (coordIdem k n)))) (n : ℕ) ↦
        (structureSheaf (isAdic_bot_pi k)).obj.map
          (homOfLE (le_iSup (fun i : ℕ ↦ basicOpen (coordIdem k i)) n)).op s) := by
  let hI := isAdic_bot_pi k
  intro y
  have hcompat (i j : ℕ) :
      (structureSheaf hI).obj.map (homOfLE inf_le_left).op (y i) =
        (structureSheaf hI).obj.map (homOfLE inf_le_right).op (y j) := by
    by_cases hij : i = j
    · subst hij
      rfl
    · have hbot : basicOpen (coordIdem k i) ⊓ basicOpen (coordIdem k j) = ⊥ :=
        (disjoint_basicOpen_coordIdem k hij).eq_bot
      have : Subsingleton
          ((structureSheaf hI).obj.obj (op (basicOpen (coordIdem k i) ⊓
            basicOpen (coordIdem k j)))) :=
        hbot ▸ subsingleton_sections_bot hI
      exact Subsingleton.elim _ _
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (structureSheaf hI)
    (fun n : ℕ ↦ basicOpen (coordIdem k n)) (⨆ n : ℕ, basicOpen (coordIdem k n))
    (fun n ↦ homOfLE (le_iSup (fun i : ℕ ↦ basicOpen (coordIdem k i)) n)) le_rfl y hcompat
  exact ⟨s, funext hs⟩

/-- Ring isomorphism `Γ(U, O_{Spf (ℕ → k)}) ≃+* (ℕ → k)` over `U = ⋃ n : ℕ, D(eₙ)`. -/
private noncomputable def sectionsInfiniteUnionRingEquiv :
    ((structureSheaf (isAdic_bot_pi k)).obj.obj
      (op (⨆ n : ℕ, basicOpen (coordIdem k n)))) ≃+* (ℕ → k) :=
  let hI := isAdic_bot_pi k
  let U : Opens (carrier (ℕ → k)) := ⨆ n : ℕ, basicOpen (coordIdem k n)
  let _ := quotientSectionsTopology hI U
  let _ (n : ℕ) := quotientSectionsTopology hI (basicOpen (coordIdem k n))
  have hglue := quotientSectionsTopology_glue hI
    (U := U) (V := fun n : ℕ ↦ basicOpen (coordIdem k n))
    (fun n ↦ le_iSup (fun i : ℕ ↦ basicOpen (coordIdem k i)) n) le_rfl
  let φRing : ((structureSheaf hI).obj.obj (op U)) →+*
      ∀ n : ℕ, (structureSheaf hI).obj.obj (op (basicOpen (coordIdem k n))) :=
    RingHom.pi fun n ↦
      ((structureSheaf hI).obj.map
        (homOfLE (le_iSup (fun i : ℕ ↦ basicOpen (coordIdem k i)) n)).op).hom
  (RingEquiv.ofBijective φRing ⟨hglue.injective, surjective_restrict_pi_coordIdem k⟩).trans
    (RingEquiv.piCongrRight (basicOpenCoordIdemRingEquiv k))

private noncomputable def basicOpenCoordIdemHomeomorph (n : ℕ) :
    letI := quotientSectionsTopology (isAdic_bot_pi k) (basicOpen (coordIdem k n))
    letI : TopologicalSpace k := ⊥
    ((structureSheaf (isAdic_bot_pi k)).obj.obj (op (basicOpen (coordIdem k n)))) ≃ₜ k := by
  let hI := isAdic_bot_pi k
  let _ := quotientSectionsTopology hI (basicOpen (coordIdem k n))
  let _ : TopologicalSpace k := ⊥
  have hbot : quotientSectionsTopology hI (basicOpen (coordIdem k n)) = ⊥ :=
    (quotientSectionsTopology_basicOpen hI _).trans (sectionsTopology_bot_eq_bot hI _)
  exact Homeomorph.mk (basicOpenCoordIdemRingEquiv k n).toEquiv
    (by rw [hbot]; exact continuous_bot) continuous_bot

/-- `sectionsInfiniteUnionRingEquiv k` is a homeomorphism from `quotientSectionsTopology` onto
`ℕ → k` equipped with the product of discrete topologies. -/
private theorem isHomeomorph_sectionsInfiniteUnionRingEquiv :
    @IsHomeomorph
      ((structureSheaf (isAdic_bot_pi k)).obj.obj (op (⨆ n : ℕ, basicOpen (coordIdem k n))))
      (ℕ → k)
      (quotientSectionsTopology (isAdic_bot_pi k) (⨆ n : ℕ, basicOpen (coordIdem k n)))
      (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥)
      (sectionsInfiniteUnionRingEquiv k) := by
  let hI := isAdic_bot_pi k
  let U : Opens (carrier (ℕ → k)) := ⨆ n : ℕ, basicOpen (coordIdem k n)
  let _ := quotientSectionsTopology hI U
  let _ (n : ℕ) := quotientSectionsTopology hI (basicOpen (coordIdem k n))
  have hglue := quotientSectionsTopology_glue hI
    (U := U) (V := fun n : ℕ ↦ basicOpen (coordIdem k n))
    (fun n ↦ le_iSup (fun i : ℕ ↦ basicOpen (coordIdem k i)) n) le_rfl
  let hhomeo₁ := hglue.isEmbedding.toHomeomorphOfSurjective (surjective_restrict_pi_coordIdem k)
  let hhomeo₂ := @Homeomorph.piCongrRight ℕ _ (fun _ ↦ k)
    (fun n ↦ quotientSectionsTopology hI (basicOpen (coordIdem k n))) (fun _ ↦ ⊥)
    (basicOpenCoordIdemHomeomorph k)
  let hhomeo := @Homeomorph.trans _ _ _
    (quotientSectionsTopology hI U)
    (@Pi.topologicalSpace ℕ _ fun n ↦ quotientSectionsTopology hI (basicOpen (coordIdem k n)))
    (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥) hhomeo₁ hhomeo₂
  have heq : (sectionsInfiniteUnionRingEquiv k : _ → _) = hhomeo.toFun := by
    ext s n
    rfl
  have hh := @Homeomorph.isHomeomorph _ _
    (quotientSectionsTopology hI U)
    (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥) hhomeo
  exact heq.symm ▸ hh

/-- Over `A = ℕ → k` with the discrete topology (`I = ⊥`) and `U = ⋃ n : ℕ, D(eₙ)`, the basic
opens `D(eₙ)` are pairwise disjoint singletons whose union `U` is not quasi-compact; there is a
ring isomorphism `Γ(U, O_{Spf A}) ≃+* (ℕ → k)` that is also a homeomorphism from
`quotientSectionsTopology` onto `∏ n : ℕ, k` (with discrete factors); and consequently
`quotientSectionsTopology` on `U` is not discrete and is strictly finer than `sectionsTopology`
(Stacks Project, Tag 0AHY). -/
example :
    let hI := isAdic_bot_pi k
    let U : Opens (carrier (ℕ → k)) := ⨆ n : ℕ, basicOpen (coordIdem k n)
    Pairwise (Disjoint on fun n : ℕ ↦ basicOpen (coordIdem k n)) ∧
      (∀ n : ℕ, Nonempty (Unique (basicOpen (coordIdem k n)))) ∧
      ¬ IsCompact (U : Set (carrier (ℕ → k))) ∧
      (∃ e : ((structureSheaf hI).obj.obj (op U)) ≃+* (ℕ → k),
        @IsHomeomorph ((structureSheaf hI).obj.obj (op U)) (ℕ → k)
          (quotientSectionsTopology hI U)
          (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥) e) ∧
      ¬ @DiscreteTopology _ (quotientSectionsTopology hI U) ∧
      sectionsTopology hI U < quotientSectionsTopology hI U := by
  let hI := isAdic_bot_pi k
  let U : Opens (carrier (ℕ → k)) := ⨆ n : ℕ, basicOpen (coordIdem k n)
  have he_homeo := isHomeomorph_sectionsInfiniteUnionRingEquiv k
  have hndisc : ¬ @DiscreteTopology _ (quotientSectionsTopology hI U) := fun hd ↦ by
    have hhomeo := @IsHomeomorph.homeomorph _ _
      (quotientSectionsTopology hI U)
      (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥) _ he_homeo
    exact not_discreteTopology_pi_bot k
      (@Homeomorph.discreteTopology_iff _ _
        (quotientSectionsTopology hI U)
        (@Pi.topologicalSpace ℕ (fun _ ↦ k) fun _ ↦ ⊥) hhomeo |>.mp hd)
  have hlt : sectionsTopology hI U < quotientSectionsTopology hI U := by
    rw [sectionsTopology_bot_eq_bot hI U, bot_lt_iff_ne_bot]
    rintro hbotU
    exact hndisc (hbotU ▸ discreteTopology_bot _)
  exact ⟨disjoint_basicOpen_coordIdem k, fun n ↦ ⟨uniqueBasicOpenCoordIdem k n⟩,
    not_isCompact_iSup_basicOpen_coordIdem k,
    ⟨sectionsInfiniteUnionRingEquiv k, he_homeo⟩, hndisc, hlt⟩

end SpfInfiniteProductChecks

end TauCeti
