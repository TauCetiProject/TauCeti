/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Projection
import Mathlib.RingTheory.SimpleModule.Basic
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.PGroupInvariants
import TauCeti.RingTheory.Idempotents.Jacobson

/-!
# The Brauer projection at a normal `p`-subgroup

Let `k` be a field of characteristic `p`, `G` a finite group and `Q` a normal `p`-subgroup of
`G`. A nonzero idempotent of `k[G]` fixed by conjugation by `Q` has nonzero Brauer projection at
`Q`. This is the step of Webb, Corollary 12.3.4, pp. 236–237, that does not involve blocks.

* `Q` acts trivially on every irreducible representation `ρ` of `G`
  (`Representation.IsIrreducible.comp_eq_trivial_of_isPGroup`). So for `z ∈ k[G]` fixed by
  conjugation by `Q`, `ρ(z) = ∑_g z_g ρ(g)` is a sum of a function constant on the orbits of `Q`
  acting on `G` by conjugation; the orbits have `p`-power size, and the sum is the sum over the
  fixed points `C_G(Q)`. If `Br_Q(z) = 0`, the coefficients of `z` vanish there and `ρ(z) = 0`
  (`TauCeti.asAlgebraHom_eq_zero_of_brauerProjection_eq_zero`).
* An idempotent `e` of `k[G]` acting as `0` on every simple module lies in every maximal left
  ideal, hence in the Jacobson radical, and so is `0` (`IsIdempotentElem.eq_zero_of_mem_jacobson`).
  Thus a nonzero `Q`-invariant idempotent `e` has `Br_Q(e) ≠ 0`
  (`TauCeti.brauerProjection_ne_zero_of_isPGroup_of_normal`).

## Main results

* `TauCeti.asAlgebraHom_eq_zero_of_brauerProjection_eq_zero`: an element of `k[G]^Q` with
  `Br_Q(z) = 0` acts as `0` on every irreducible representation.
* `TauCeti.brauerProjection_ne_zero_of_isPGroup_of_normal`: a nonzero idempotent of `k[G]^Q` has
  nonzero Brauer projection at `Q`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Corollary 12.3.4, pp. 236–237.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]
  {Q : Subgroup G} [Q.Normal]

/-- **An element with vanishing Brauer projection at a normal `p`-subgroup acts as zero on every
irreducible representation.** Let `Q` be a normal `p`-subgroup of a finite group `G` and `k` a
field of characteristic `p`. If `z ∈ k[G]` is fixed by conjugation by `Q` and `Br_Q(z) = 0`, then
`z` acts as `0` on every irreducible representation of `G`. -/
theorem asAlgebraHom_eq_zero_of_brauerProjection_eq_zero (hQ : IsPGroup p Q)
    {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    (hρ : Representation.IsIrreducible ρ)
    {z : MonoidAlgebra k G} (hz : z ∈ conjInvariants k Q) (hBr : brauerProjection Q z = 0) :
    ρ.asAlgebraHom z = 0 := by
  classical
  have := Fintype.ofFinite G
  have htriv := hρ.comp_eq_trivial_of_isPGroup p Q hQ
  have hq (g : G) (hg : g ∈ Q) : ρ g = 1 := by
    ext v
    simpa [Representation.trivial_apply] using congrArg (fun σ => σ ⟨g, hg⟩ v) htriv
  let : MulAction Q G := MulAction.compHom G (MulAut.conj.comp Q.subtype)
  have hsmul (q : Q) (a : G) : q • a = q * a * (q : G)⁻¹ := by
    rw [MulAction.compHom_smul_def]
    simp
  rw [ρ.asAlgebraHom_eq_sum z,
    IsPGroup.sum_eq_sum_fixedPoints_of_nsmul_eq_zero hQ (fun x => ?_) _ fun q a => ?_]
  · refine Finset.sum_eq_zero fun g hg => ?_
    have hg' : g ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hqQ
      have := (Finset.mem_filter.1 hg).2 ⟨q, hqQ⟩
      rw [hsmul, mul_inv_eq_iff_eq_mul] at this
      exact this
    have := (brauerProjection_eq_zero_iff.1 hBr) g hg'
    rw [this, zero_smul]
  · rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  · simp [hsmul, (mem_conjInvariants_iff_coeff.1 hz) q q.property a, hq]

/-- **A nonzero idempotent fixed by a normal `p`-subgroup has nonzero Brauer projection there.**
Let `Q` be a normal `p`-subgroup of a finite group `G` and `k` a field of characteristic `p`.
If `e ∈ k[G]^Q` is a nonzero idempotent, then `Br_Q(e) ≠ 0`. -/
theorem brauerProjection_ne_zero_of_isPGroup_of_normal (hQ : IsPGroup p Q)
    {e : MonoidAlgebra k G} (he : e ∈ conjInvariants k Q) (hidem : IsIdempotentElem e)
    (hne : e ≠ 0) : brauerProjection Q e ≠ 0 := by
  intro hBr
  -- `e` lies in every maximal left ideal `m`: it acts as `0` on the simple module `k[G] ⧸ m`.
  have hmem (m : Ideal (MonoidAlgebra k G)) (hm : m.IsMaximal) : e ∈ m := by
    have : IsSimpleModule (MonoidAlgebra k G) (MonoidAlgebra k G ⧸ m) :=
      isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hm)
    have hρ := (Representation.isIrreducible_ofModule'_iff
      (k := k) (G := G) (MonoidAlgebra k G ⧸ m)).2 this
    have h0 := congrArg (fun f => f (Submodule.Quotient.mk 1))
      (asAlgebraHom_eq_zero_of_brauerProjection_eq_zero hQ hρ he hBr)
    simp only [Representation.asAlgebraHom_ofModule'_apply, LinearMap.zero_apply,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  -- So `e` is an idempotent in the Jacobson radical, hence `0`.
  exact hne (hidem.eq_zero_of_mem_jacobson (by
    rw [Ring.jacobson_eq_sInf_isMaximal]; exact Submodule.mem_sInf.2 hmem))

end TauCeti
