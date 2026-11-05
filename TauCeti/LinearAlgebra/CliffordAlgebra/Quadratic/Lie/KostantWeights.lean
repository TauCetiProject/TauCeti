/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Separation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.RootWeights
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

import TauCeti.Algebra.Lie.HighestWeight.Weight.Lattice
import TauCeti.Algebra.Lie.Weights.Basic
import TauCeti.Algebra.Lie.Weights.Killing.QuadraticForm
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Square
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Subalgebra
import TauCeti.LinearAlgebra.Eigenspace.Involution
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# The weights of Kostant's module

Let `L` be a Lie algebra with nondegenerate Killing form over a field of characteristic zero, with
a splitting Cartan subalgebra `H`, and fix a base of its root system. For each root `α`, let
`X_α = β(e_α, f_α)` be the Clifford bivector of root vectors `e_α ∈ L_α` and `f_α ∈ L_{-α}` with
Killing pairing `1`. These vectors form a hyperbolic pair, so `X_α` is an involution, and the
hyperbolic planes of distinct positive roots are mutually orthogonal, so the `X_α` commute. The
quadratic lift of `h ∈ H` is

`q(h) = 1 / 2 • ∑_{α > 0} α(h) • X_α`.

Hence every joint eigenvalue of the lift of `H` on the Clifford algebra is `1 / 2 • ∑_{α > 0} ±α`:
in Kostant's left-regular module, every weight has the form `ρ - ∑_{α ∈ S} α` for a set `S` of
positive roots, with `ρ` the half-sum of the positive roots.

Such a weight lies below `ρ`, and this is what singles out `ρ` among the highest weights of the
module. A highest weight `lam` is dominant integral, so if it has the same Casimir scalar as `ρ`,
then `lam = ρ`.

## Main results

* `CliffordAlgebra.exists_eq_weylVector_sub_sum_kostant_of_forall_lie_eq_smul`: every weight of
  Kostant's module is `ρ` minus a sum of distinct positive roots.
* `CliffordAlgebra.eq_weylVector_of_isHighestWeightVector_kostant_of_casimirScalar_eq`: a highest
  weight of Kostant's module with the Casimir scalar of `ρ` is `ρ`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapters
  5--10.
-/

public section

universe u v

open TauCeti LieAlgebra LieModule TauCeti.LieAlgebra

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] [CharZero K]
  {L : Type v} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The element `X_χ = ∑ᵢ β(π_χ bᵢ, π_{-χ} b'ᵢ)` of the Clifford algebra, for a basis `b` of `L`
with Killing-dual basis `b'`. By `adjointCliffordHom_cartan_eq_sum_posRoots` the lift of a Cartan
element is a combination of these elements. -/
private noncomputable def rootInvolution (χ : Weight K H L) :
    CliffordAlgebra (killingQuadraticForm K L) :=
  ∑ i, bivector (killingQuadraticForm K L)
    (genWeightSpaceProjection K H L χ (Module.finBasis K L i))
    (genWeightSpaceProjection K H L (-χ) (killingDualBasis (Module.finBasis K L) i))

/-- The element `X_χ` is the bivector of a hyperbolic pair of root vectors: the root space of `χ`
is a line, so the sum defining `X_χ` collapses, and the Killing pairing of the pair is the trace of
the projection onto that line. -/
private theorem exists_rootInvolution_eq_bivector {χ : Weight K H L} (hχ : χ.IsNonZero) :
    ∃ e ∈ rootSpace H χ, ∃ f ∈ rootSpace H (-χ : Weight K H L), killingForm K L e f = 1 ∧
      rootInvolution H χ = bivector (killingQuadraticForm K L) e f := by
  obtain ⟨v, -, hv⟩ := (finrank_eq_one_iff' (K := K) (V := rootSpace H χ)).mp
    (IsKilling.finrank_rootSpace_eq_one χ hχ)
  let bs := Module.finBasis K L
  let y := fun i ↦ genWeightSpaceProjection K H L (-χ) (killingDualBasis bs i)
  choose s hs using fun i ↦ hv ⟨genWeightSpaceProjection K H L χ (bs i),
    genWeightSpaceProjection_apply_mem χ (bs i)⟩
  have hs' (i) : s i • (v : L) = genWeightSpaceProjection K H L χ (bs i) := by
    simpa using congrArg Subtype.val (hs i)
  refine ⟨v, v.2, ∑ i, s i • y i, sum_mem fun i _ ↦ Submodule.smul_mem _ _
    (genWeightSpaceProjection_apply_mem _ _), ?_, ?_⟩
  · have hpair (i) : killingForm K L (v : L) (s i • y i) =
        killingForm K L (killingDualBasis bs i) (genWeightSpaceProjection K H L χ (bs i)) := by
      have hmove : killingForm K L (v : L) (s i • y i) = killingForm K L (s i • (v : L)) (y i) := by
        simp only [map_smul, LinearMap.smul_apply]
      rw [hmove, hs' i, killingForm_genWeightSpaceProjection H χ,
        genWeightSpaceProjection_apply_apply, ← killingForm_genWeightSpaceProjection H χ,
        LieModule.traceForm_comm]
    rw [map_sum, Finset.sum_congr rfl fun i _ ↦ hpair i,
      LinearMap.BilinForm.sum_apply_dualBasis_eq_trace, trace_genWeightSpaceProjection_eq_one H hχ]
  · simp only [rootInvolution, ← hs', ← bivectorBilinear_apply, map_sum, map_smul,
      LinearMap.smul_apply, bs, y]

/-- The element `X_χ` of a nonzero weight is an involution. -/
private theorem rootInvolution_mul_self {χ : Weight K H L} (hχ : χ.IsNonZero) :
    rootInvolution H χ * rootInvolution H χ = 1 := by
  obtain ⟨e, he, f, hf, hef, hX⟩ := exists_rootInvolution_eq_bivector H hχ
  rw [hX, bivector_mul_self, killingQuadraticForm_eq_zero_of_mem_rootSpace H hχ he,
    killingQuadraticForm_eq_zero_of_mem_rootSpace H (Weight.IsNonZero.neg hχ) hf,
    polar_killingQuadraticForm, hef, mul_one, invOf_mul_self, one_pow, mul_zero, sub_zero, map_one]

/-- The elements `X_χ` and `X_ψ` commute unless `ψ = ± χ`: they are bivectors of mutually orthogonal
hyperbolic pairs. -/
private theorem commute_rootInvolution {χ ψ : Weight K H L} (hχ : χ.IsNonZero) (hψ : ψ.IsNonZero)
    (hne : χ ≠ ψ) (hne' : χ ≠ -ψ) : Commute (rootInvolution H χ) (rootInvolution H ψ) := by
  obtain ⟨e, he, f, hf, -, hX⟩ := exists_rootInvolution_eq_bivector H hχ
  obtain ⟨e', he', f', hf', -, hX'⟩ := exists_rootInvolution_eq_bivector H hψ
  rw [hX, hX', commute_iff_lie_eq, lie_bivector_bivector,
    polar_killingQuadraticForm_eq_zero_of_mem_rootSpace H he he'
      (weight_add_ne_zero_of_ne_neg hne'),
    polar_killingQuadraticForm_eq_zero_of_mem_rootSpace H he hf'
      (weight_add_ne_zero_of_ne_neg (by rwa [neg_neg])),
    polar_killingQuadraticForm_eq_zero_of_mem_rootSpace H hf he'
      (weight_add_ne_zero_of_ne_neg (by rwa [ne_eq, neg_inj])),
    polar_killingQuadraticForm_eq_zero_of_mem_rootSpace H hf hf'
      (weight_add_ne_zero_of_ne_neg (by rwa [neg_neg, ne_eq, neg_eq_iff_eq_neg]))]
  simp [bivector_def]

variable {H}
variable (base : (IsKilling.rootSystem H).Base)

/-- The lift of a Cartan element in terms of the elements `X_α` of the positive roots:
`q(h) = 1 / 2 • ∑_{α > 0} α(h) • X_α`. -/
private theorem adjointCliffordHom_cartan_eq_sum_rootInvolution (h : H) :
    adjointCliffordHom K L (h : L) =
      (2 : K)⁻¹ • ∑ a ∈ posRootsFinset (IsKilling.rootSystem H) base,
        (a : Weight K H L) h • rootInvolution H (a : Weight K H L) := by
  simpa only [rootInvolution] using
    adjointCliffordHom_cartan_eq_sum_posRoots H (Module.finBasis K L) base h

/-- The elements `X_α` of the positive roots commute with one another. -/
private theorem commute_rootInvolution_of_mem_posRootsFinset {a b : H.root}
    (ha : a ∈ posRootsFinset (IsKilling.rootSystem H) base)
    (hb : b ∈ posRootsFinset (IsKilling.rootSystem H) base) :
    Commute (rootInvolution H (a : Weight K H L)) (rootInvolution H (b : Weight K H L)) := by
  by_cases hab : a = b
  · rw [hab]
  refine commute_rootInvolution H (H.isNonZero_coe_root a) (H.isNonZero_coe_root b)
    (fun h ↦ hab (Subtype.ext h)) fun h ↦ ?_
  have hneg : a = -b := Subtype.ext (h.trans IsKilling.val_neg_root.symm)
  rw [mem_posRootsFinset] at ha hb
  refine reflectionPerm_self_notMem_posRoots _ base hb ?_
  rwa [IsKilling.rootSystem_reflectionPerm_self_eq_neg, ← hneg]

/-- Inside any joint eigenspace of the lift of the Cartan subalgebra, the commuting involutions
`X_α` have a joint eigenvector. -/
private theorem exists_forall_rootInvolution_mul_eq {c : CliffordAlgebra (killingQuadraticForm K L)}
    (hc : c ≠ 0) {mu : H → K} (hmu : ∀ h : H, adjointCliffordHom K L (h : L) * c = mu h • c) :
    ∃ v : CliffordAlgebra (killingQuadraticForm K L), v ≠ 0 ∧
      (∀ h : H, adjointCliffordHom K L (h : L) * v = mu h • v) ∧
      ∀ a ∈ posRootsFinset (IsKilling.rootSystem H) base,
        rootInvolution H (a : Weight K H L) * v = v ∨
          rootInvolution H (a : Weight K H L) * v = -v := by
  classical
  let Φ := posRootsFinset (IsKilling.rootSystem H) base
  let W : Submodule K (CliffordAlgebra (killingQuadraticForm K L)) :=
    ⨅ h : H, Module.End.eigenspace (LinearMap.mulLeft K (adjointCliffordHom K L (h : L))) (mu h)
  have hmem {w} : w ∈ W ↔ ∀ h : H, adjointCliffordHom K L (h : L) * w = mu h • w := by
    simp [W, Submodule.mem_iInf]
  have hstable (a : Φ) : ∀ w ∈ W,
      LinearMap.mulLeft K (rootInvolution H ((a : H.root) : Weight K H L)) w ∈ W := fun w hw ↦ by
    refine hmem.2 fun h ↦ ?_
    have hcomm : Commute (adjointCliffordHom K L (h : L))
        (rootInvolution H ((a : H.root) : Weight K H L)) := by
      rw [adjointCliffordHom_cartan_eq_sum_rootInvolution base h]
      exact (Commute.sum_left _ _ _ fun b hb ↦
        (commute_rootInvolution_of_mem_posRootsFinset base hb a.2).smul_left _).smul_left _
    rw [LinearMap.mulLeft_apply, ← mul_assoc, hcomm.eq, mul_assoc, hmem.1 hw h, mul_smul_comm]
  let f (a : Φ) : Module.End K W :=
    (LinearMap.mulLeft K (rootInvolution H ((a : H.root) : Weight K H L))).restrict (hstable a)
  have hf (a : Φ) (w : W) :
      ((f a w : W) : CliffordAlgebra (killingQuadraticForm K L)) =
        rootInvolution H ((a : H.root) : Weight K H L) * w := by
    simp [f]
  have : Nontrivial W := ⟨⟨c, hmem.2 hmu⟩, 0, fun h ↦ hc (congrArg Subtype.val h)⟩
  have htri (a : Φ) : ⨆ μ, (f a).maxGenEigenspace μ = ⊤ := by
    have hinv : Function.Involutive (f a) := fun w ↦ Subtype.ext <| by
      rw [hf, hf, ← mul_assoc, rootInvolution_mul_self H (H.isNonZero_coe_root _), one_mul]
    exact top_unique <| (Module.End.iSup_eigenspace_eq_top_of_involutive hinv).ge.trans <|
      iSup_mono fun _ ↦ Module.End.eigenspace_le_maxGenEigenspace
  obtain ⟨t, v, hv0, hv⟩ := exists_jointEigenvector_of_pairwise_commute f
    (fun a b _ ↦ LinearMap.ext fun w ↦ Subtype.ext <| by
      simp only [mul_apply_eq_comp, hf, ← mul_assoc,
        (commute_rootInvolution_of_mem_posRootsFinset base a.2 b.2).eq]) htri
  refine ⟨v, fun h ↦ hv0 (Subtype.ext h), hmem.1 v.2, fun a ha ↦ ?_⟩
  have heig : rootInvolution H (a : Weight K H L) * v = t ⟨a, ha⟩ • (v : _) := by
    simpa only [Submodule.coe_smul, hf] using
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 (hv ⟨a, ha⟩))
  have hsq : t ⟨a, ha⟩ * t ⟨a, ha⟩ = 1 := by
    have h1 : (t ⟨a, ha⟩ * t ⟨a, ha⟩) • (v : CliffordAlgebra (killingQuadraticForm K L)) =
        (1 : K) • (v : CliffordAlgebra (killingQuadraticForm K L)) := by
      rw [one_smul, mul_smul, ← heig, ← mul_smul_comm, ← heig, ← mul_assoc,
        rootInvolution_mul_self H (H.isNonZero_coe_root a), one_mul]
    exact smul_left_injective K (fun h ↦ hv0 (Subtype.ext h)) h1
  rcases mul_self_eq_one_iff.1 hsq with ht | ht
  · exact Or.inl (by rw [heig, ht, one_smul])
  · exact Or.inr (by rw [heig, ht, neg_one_smul])

/-- **The weights of Kostant's module**: if the Cartan subalgebra acts on a nonzero vector of
Kostant's module through `mu`, then `mu = ρ - ∑_{α ∈ S} α` for a set `S` of positive roots. -/
theorem exists_eq_weylVector_sub_sum_kostant_of_forall_lie_eq_smul
    {c : CliffordAlgebra (killingQuadraticForm K L)} (hc : c ≠ 0) {mu : H → K}
    (hmu : ∀ h : H, ⁅(h : L), c⁆ = mu h • c) :
    ∃ S ⊆ posRootsFinset (IsKilling.rootSystem H) base,
      mu = ⇑(weylVector (IsKilling.rootSystem H) base -
        ∑ a ∈ S, (IsKilling.rootSystem H).root a) := by
  classical
  obtain ⟨v, hv0, hv, hX⟩ := exists_forall_rootInvolution_mul_eq base hc (mu := mu)
    (fun h ↦ by rw [← kostant_lie_def, hmu h])
  set Φ := posRootsFinset (IsKilling.rootSystem H) base with hΦ
  let p (a : H.root) : Prop := rootInvolution H (a : Weight K H L) * v = -v
  refine ⟨Φ.filter p, Finset.filter_subset _ _, funext fun h ↦ ?_⟩
  have hneg : ∑ a ∈ Φ.filter p, (a : Weight K H L) h • (rootInvolution H (a : Weight K H L) * v) =
      (-∑ a ∈ Φ.filter p, (a : Weight K H L) h) • v := by
    rw [neg_smul, Finset.sum_smul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a ha ↦ by rw [(Finset.mem_filter.1 ha).2, smul_neg]
  have hpos :
      ∑ a ∈ Φ.filter (¬ p ·), (a : Weight K H L) h • (rootInvolution H (a : Weight K H L) * v) =
        (∑ a ∈ Φ.filter (¬ p ·), (a : Weight K H L) h) • v := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have ⟨ha₁, ha₂⟩ := Finset.mem_filter.1 ha
    rw [(hX a ha₁).resolve_right ha₂]
  have hρ : weylVector (IsKilling.rootSystem H) base h =
      (2 : K)⁻¹ * (∑ a ∈ Φ.filter p, (a : Weight K H L) h +
        ∑ a ∈ Φ.filter (¬ p ·), (a : Weight K H L) h) := by
    rw [Finset.sum_filter_add_sum_filter_not, weylVector_def, twoWeylVector_def, invOf_eq_inv,
      LinearMap.smul_apply, LinearMap.sum_apply]
    simp [hΦ]
  have hroot : (∑ a ∈ Φ.filter p, (IsKilling.rootSystem H).root a) h =
      ∑ a ∈ Φ.filter p, (a : Weight K H L) h := by
    simp
  refine smul_left_injective K hv0 ?_
  simp only [LinearMap.sub_apply, hρ, hroot]
  rw [← hv h, adjointCliffordHom_cartan_eq_sum_rootInvolution base h, ← hΦ, smul_mul_assoc,
    Finset.sum_mul, Finset.sum_congr rfl fun a _ ↦ smul_mul_assoc _ _ _,
    ← Finset.sum_filter_add_sum_filter_not Φ p, hneg, hpos, ← add_smul, smul_smul]
  congr 1
  ring

/-- **A highest weight of Kostant's module with the Casimir scalar of `ρ` is `ρ`.** Every highest
weight of the module is a dominant integral weight lying below `ρ`, and the Casimir scalar separates
`ρ` from the dominant integral weights below it. -/
theorem eq_weylVector_of_isHighestWeightVector_kostant_of_casimirScalar_eq
    {lam : Module.Dual K H} {c : CliffordAlgebra (killingQuadraticForm K L)}
    (hv : IsHighestWeightVector base lam c)
    (hcas : casimirScalar base lam =
      casimirScalar base (weylVector (IsKilling.rootSystem H) base)) :
    lam = weylVector (IsKilling.rootSystem H) base := by
  -- `TauCeti.isDominantIntegral_weylVector` fixes the instance `invertibleTwo`.
  obtain rfl : ‹Invertible (2 : K)› = invertibleTwo := Subsingleton.elim _ _
  by_contra hne
  obtain ⟨S, hS, hlam⟩ := exists_eq_weylVector_sub_sum_kostant_of_forall_lie_eq_smul base
    hv.ne_zero hv.lie_eq_smul
  have hcone : weylVector (IsKilling.rootSystem H) base - lam ∈
      posRootCone (IsKilling.rootSystem H) base := by
    rw [DFunLike.coe_injective hlam, sub_sub_cancel]
    exact sum_mem fun a ha ↦ root_mem_posRootCone_of_mem_posRoots _ base
      ((mem_posRootsFinset _ base a).1 (hS ha))
  exact (isDominantIntegral_weylVector (b := base)
    |>.casimirScalar_ne_casimirScalar_of_isDominantIntegral_of_sub_mem_posRootCone_of_ne
      hv.isDominantIntegral hcone hne) hcas.symm

end CliffordAlgebra
