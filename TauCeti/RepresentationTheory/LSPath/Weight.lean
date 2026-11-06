/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic

/-!
# Lattice-valued endpoints of Lakshmibai–Seshadri paths

The endpoint of an LS path is a rational convex combination of orbit weights. Its break-chain
conditions imply more than integrality of its pairings: the endpoint is the image of a weight
in the original character lattice. This supplies the lattice-valued endpoints needed to equip LS
encodings with a crystal structure, including when the roots do not span the character lattice.

Summation by parts expresses the endpoint as the last orbit weight plus the sum of the
corrections `a_j (τ_{j-1} λ - τ_j λ)`. Each correction is the image of an integral root-lattice
vector, because each edge of its `a_j`-chain is a root multiplied by an integral coefficient.
Thus the endpoint differs from the last orbit weight by an actual root-lattice vector.
No injectivity or spanning assumption is needed for this existence result; injectivity of a
chosen realization then gives uniqueness of the lattice weight.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Summation by parts for the endpoint of an LS path: the last orbit weight plus its
break-time-weighted changes of direction. -/
theorem endpoint_toPLPath_eq_last_add_sum (π : LSPath P b lam) (f : M →+ V) :
    (π.toPLPath 𝕜 f).endpoint = f ((π.dir (Fin.last _)).1 • lam) +
      ∑ j : Fin π.length, (π.time j.castSucc.succ : 𝕜) •
        (f ((π.dir j.castSucc).1 • lam) - f ((π.dir j.succ).1 • lam)) := by
  rw [endpoint_toPLPath]
  simp only [duration_def, Rat.cast_sub, sub_smul, smul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun j : Fin (π.length + 1) ↦
    (π.time j.succ : 𝕜) • f ((π.dir j).1 • lam)),
    Fin.sum_univ_succ (fun j : Fin (π.length + 1) ↦
      (π.time j.castSucc : 𝕜) • f ((π.dir j).1 • lam))]
  simp only [Fin.succ_last, π.time_last, Rat.cast_one, one_smul, Fin.castSucc_zero,
    π.time_zero, Rat.cast_zero, zero_smul, zero_add, Fin.succ_castSucc]
  abel

variable [P.flip.IsReduced]

/-- The endpoint of an LS path of dominant shape differs from its last orbit weight by the
image of an integral root-lattice vector. This is a lattice statement, not only integrality
of scalar pairings. -/
theorem exists_mem_rootSpan_endpoint_eq_add (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) :
    ∃ m ∈ P.rootSpan ℤ,
      (π.toPLPath 𝕜 f).endpoint = f ((π.dir (Fin.last _)).1 • lam + m) := by
  classical
  have hcorrection (j : Fin π.length) : ∃ m ∈ P.rootSpan ℤ,
      (π.time j.castSucc.succ : 𝕜) •
        (f ((π.dir j.castSucc).1 • lam) - f ((π.dir j.succ).1 • lam)) = f m := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j
    simpa only [hhead, hlast] using hC.exists_mem_rootSpan_smul_sub_eq hlam f
  choose m hm heq using hcorrection
  refine ⟨∑ j, m j, Submodule.sum_mem _ (fun j _ ↦ hm j), ?_⟩
  rw [π.endpoint_toPLPath_eq_last_add_sum f, map_add, map_sum]
  simp only [heq]

/-- Every realized LS endpoint is the image of a weight in the original lattice. When the
realization is injective, that weight is unique. -/
theorem existsUnique_endpoint_eq (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (hf : Function.Injective f) :
    ∃! μ : M, (π.toPLPath 𝕜 f).endpoint = f μ := by
  obtain ⟨m, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) hlam f
  exact ⟨_, hm, fun μ hμ ↦ hf (hμ.symm.trans hm)⟩

end TauCeti.LSPath
