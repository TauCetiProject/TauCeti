/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination

/-!
# Radicals and separated coordinate groups

The coordinate group of a system of group equations is separated by the group in which its
points are taken: a nonidentity class is detected by evaluation at some solution. More
generally, a normal subgroup of `G[X]` is a radical exactly when its quotient is separated.
Consequently the radical of a system equals its defining normal closure exactly when the
group presented by that system is separated.

The radical quotient has a universal property among separated groups with coefficients:
every coefficient-preserving homomorphism from the defining group to a separated group
factors uniquely through the coordinate group. This distinguishes a coordinate group from
the group presented by the original equations. For example, over a torsion-free point group,
the group defined by `x ^ n = 1` is not separated when `n > 1`.

All coefficient maps are arbitrary homomorphisms. In particular these statements include
inconsistent systems: their coordinate groups are trivial, while their defining groups are
separated only if they too are trivial. No finiteness, domain, or Noetherian hypothesis is used.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.4, Corollary 8.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group I*,
  J. Algebra 200 (1998), §1, Lemma 3.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup

variable {G H K X : Type*} [Group G] [Group H] [Group K]
  {ι : G →* H} {ιK : G →* K} {S : Set (GX G X)}

namespace GX

/-- Pulling back the intersection of all coefficient-preserving kernels on `G[X] / N`
recovers the ideal of the solutions of `N`, including when there are no solutions. -/
theorem comap_iInf_ker_quotientCoeff (ι : G →* H) (N : Subgroup (GX G X)) [N.Normal] :
    (⨅ φ : GHom (quotientCoeff N) ι, (φ : GX G X ⧸ N →* H).ker).comap
      (QuotientGroup.mk' N) = I ι (V ι (N : Set (GX G X))) := by
  ext w
  simp only [mem_comap, mem_iInf, MonoidHom.mem_ker, QuotientGroup.mk'_apply,
    MonoidHom.coe_ofClass, mem_I]
  constructor
  · intro h v hv
    simpa only [quotientEvalGHom_mk] using h (quotientEvalGHom v hv)
  · intro h φ
    have heval := DFunLike.congr_fun (eval_eq_comp_mk' φ) w
    have hv := (quotientHomEquiv ι N φ).2
    have hpoint : (fun x => φ (inr (FreeGroup.of x) : GX G X)) =
        (quotientHomEquiv ι N φ : X → H) :=
      funext fun x => (quotientHomEquiv_apply_coe φ x).symm
    rw [hpoint] at heval
    simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MonoidHom.coe_ofClass]
      using heval.symm.trans (h _ hv)

/-- A normal subgroup is the ideal of its solutions exactly when its quotient is separated
by the point group through coefficient-preserving homomorphisms. -/
theorem isSeparatedBy_quotientCoeff_iff (ι : G →* H) (N : Subgroup (GX G X)) [N.Normal] :
    IsSeparatedBy (quotientCoeff N) ι ↔ I ι (V ι (N : Set (GX G X))) = N := by
  rw [isSeparatedBy_iff_iInf_ker,
    ← (comap_injective (QuotientGroup.mk'_surjective N)).eq_iff]
  simp only [comap_iInf_ker_quotientCoeff, MonoidHom.comap_bot, QuotientGroup.ker_mk']

end GX

/-- Every coordinate group is separated by its point group. Each nonidentity class is
detected by evaluation at a solution of the defining system. -/
theorem CoordGroup.isSeparatedBy (ι : G →* H) (S : Set (GX G X)) :
    IsSeparatedBy (CoordGroup.coeff ι S) ι := by
  have hcoeff : CoordGroup.coeff ι S = GX.quotientCoeff (Rad ι S) :=
    MonoidHom.ext fun g => by simp
  rw [hcoeff]
  apply (GX.isSeparatedBy_quotientCoeff_iff ι (Rad ι S)).2
  rw [V_Rad, ← Rad_def]

/-- The radical of a system is its defining normal closure exactly when the group presented
by that system is separated by the point group over the given coefficients. -/
theorem radical_eq_normalClosure_iff_separated (ι : G →* H) (S : Set (GX G X)) :
    Rad ι S = normalClosure S ↔ IsSeparatedBy (SystemGroup.coeff S) ι := by
  have hcoeff : SystemGroup.coeff S = GX.quotientCoeff (normalClosure S) :=
    MonoidHom.ext fun g => by simp
  rw [hcoeff]
  rw [GX.isSeparatedBy_quotientCoeff_iff, V_normalClosure, Rad_def]

/-- If a coefficient-preserving homomorphism to a separated group kills a system, it kills
its radical. -/
theorem radical_le_ker_of_isSeparatedBy (hK : IsSeparatedBy ιK ι)
    (f : GHom (inl : G →* GX G X) ιK) (hS : S ⊆ (f : GX G X →* K).ker) :
    Rad ι S ≤ (f : GX G X →* K).ker := by
  intro w hw
  by_contra hfw
  obtain ⟨φ, hφ⟩ := (isSeparatedBy_def _ _).1 hK (f w) hfw
  have hcoeff : ((φ : K →* H).comp (f : GX G X →* K)).comp inl = ι := by
    rw [MonoidHom.comp_assoc, f.comp_coeff, φ.comp_coeff]
  have heval := eval_eq_of_comp_inl hcoeff
  simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass] at heval
  have hv : (fun x => φ (f (inr (FreeGroup.of x)))) ∈ V ι S := by
    apply mem_V.2
    intro s hs
    rw [heval]
    simpa using congrArg φ (hS hs)
  have hwv := mem_Rad.1 hw _ hv
  rw [heval] at hwv
  exact hφ hwv

namespace SystemGroup

/-- An inconsistent system has a separated defining group exactly when that group is trivial.
This includes the case where there are no coefficient-preserving homomorphisms to `H`. -/
theorem isSeparatedBy_iff_subsingleton_of_V_eq_empty (hS : V ι S = ∅) :
    IsSeparatedBy (coeff S) ι ↔ Subsingleton (SystemGroup G S) := by
  rw [← radical_eq_normalClosure_iff_separated, Rad_def, hS, I_empty,
    QuotientGroup.subsingleton_iff, eq_comm]

/-- The homomorphism from the group presented by a system, before passing to its radical,
as a homomorphism on `G[X]`. -/
private def onFree (f : GHom (coeff S) ιK) : GHom (inl : G →* GX G X) ιK where
  toMonoidHom := (f : SystemGroup G S →* K).comp (QuotientGroup.mk' (normalClosure S))
  map_coeff' g := by simpa using f.map_coeff g

private theorem radical_le_ker_onFree (hK : IsSeparatedBy ιK ι)
    (f : GHom (coeff S) ιK) : Rad ι S ≤ (onFree f : GX G X →* K).ker := by
  apply radical_le_ker_of_isSeparatedBy hK (onFree f)
  intro s hs
  apply (MonoidHom.mem_ker).2
  simp only [MonoidHom.coe_ofClass, onFree, GHom.coe_mk,
    MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [(QuotientGroup.eq_one_iff s).2 (subset_normalClosure hs), map_one]

/-- A coefficient-preserving map from a defining group to a separated group descends to
the coordinate group. -/
def liftCoordGroup (hK : IsSeparatedBy ιK ι) (f : GHom (coeff S) ιK) :
    GHom (CoordGroup.coeff ι S) ιK where
  toMonoidHom := QuotientGroup.lift (Rad ι S) (onFree f : GX G X →* K)
    (radical_le_ker_onFree hK f)
  map_coeff' g := by simp [onFree]

/-- The descended map has the same values on word representatives. -/
@[simp]
theorem liftCoordGroup_mk (hK : IsSeparatedBy ιK ι) (f : GHom (coeff S) ιK)
    (w : GX G X) : liftCoordGroup hK f (w : CoordGroup ι S) = f (w : SystemGroup G S) :=
  (rfl)

/-- The descended map factors the original map through the radical quotient. -/
@[simp]
theorem liftCoordGroup_comp_toCoordGroup (hK : IsSeparatedBy ιK ι)
    (f : GHom (coeff S) ιK) :
    (liftCoordGroup hK f).comp (toCoordGroup ι S) = f := by
  apply GHom.ext
  intro q
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  simp [GHom.coe_comp]

/-- Uniqueness of the factorization through the radical quotient. -/
theorem liftCoordGroup_unique (hK : IsSeparatedBy ιK ι) (f : GHom (coeff S) ιK)
    (ψ : GHom (CoordGroup.coeff ι S) ιK) (hψ : ψ.comp (toCoordGroup ι S) = f) :
    ψ = liftCoordGroup hK f := by
  apply GHom.ext
  intro q
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  simpa [GHom.coe_comp] using DFunLike.congr_fun hψ (w : SystemGroup G S)

/-- The defining group of `x ^ n = 1` is not separated by a torsion-free point group when
`n > 1`: the nonidentity class of `x` dies under every specialization. -/
theorem not_isSeparatedBy_pow [IsMulTorsionFree H] {n : ℕ}
    (hn : 2 ≤ n) : ¬IsSeparatedBy
      (coeff {(inr (FreeGroup.of ()) : GX G Unit) ^ n}) ι := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have hx : (inr (FreeGroup.of ()) : GX G Unit) ∈
      Rad ι {(inr (FreeGroup.of ())) ^ n} := by
    apply mem_Rad.2
    intro v hv
    have hpow := mem_V.1 hv _ (Set.mem_singleton _)
    simpa [hn0] using hpow
  rw [(radical_eq_normalClosure_iff_separated ι _).2 h] at hx
  exact inr_of_notMem_normalClosure_pow (by omega) () hx

end SystemGroup

end TauCeti.GroupAlgGeom
