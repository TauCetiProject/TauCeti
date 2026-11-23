/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Vanishing
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Nilpotent
import TauCeti.Algebra.AlgebraicGroup.Hopf.Commutator
import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible

/-!
# Connected nilpotent groups have a positive-dimensional centre

Let `G` be a nontrivial smooth connected affine group over an algebraically closed field whose
group of rational points is nilpotent; for instance a nontrivial smooth connected unipotent group.
Then `G` has a nontrivial central closed subgroup whose ideal is prime, that is, a nontrivial
smooth connected central subgroup. This is the subgroup form of the classical statement that the
centre of a nontrivial connected nilpotent group has positive dimension. It supplies the
nontrivial connected central subgroups of the unipotent radical used in the structure theory of
connected solvable groups.

If the rational points form a commutative group, `G` itself is central. Otherwise there is a
rational point `y` in the second centre but not in the centre. Then `g ↦ ⁅g, y⁆` is a
homomorphism from the rational points to the centre, and it is a regular map. The closure of its
image is central, nontrivial, and irreducible: its ideal is the kernel of the coordinate map of
`g ↦ ⁅g, y⁆`, which is prime because `G` is irreducible.

## Main declarations

* `TauCeti.HopfIdeal.exists_isCentral_isPrime_ne_augmentation_of_isNilpotent`: a nontrivial
  smooth connected group with nilpotent rational points has a nontrivial irreducible central
  closed subgroup.
* `TauCeti.HopfIdeal.exists_isCentral_isPrime_ne_augmentation_of_forall_isUnipotentPoint`: the
  same for a nontrivial smooth connected unipotent group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.21, for nilpotence of unipotent groups,
  and §16.d, for the structure of connected solvable groups.
* A. Borel, *Linear Algebraic Groups*, Chapter I, §2, for closures of images of irreducible
  varieties and commutator maps.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.HopfIdeal

variable {k H : Type*} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)]

/-- The closure of the image of a regular endomorphism `ψ` of the rational points with central,
nontrivial values is a nontrivial irreducible central closed subgroup. Here `φ` is the coordinate
map realising `ψ` as a regular map. -/
private theorem exists_isCentral_isPrime_ne_augmentation_of_monoidHom
    (ψ : WithConv (H →ₐ[k] k) →* WithConv (H →ₐ[k] k))
    (hcenter : ψ.range ≤ Subgroup.center _) (hne : ψ.range ≠ ⊥) (φ : H →ₐ[k] H)
    (hφ : ∀ b : H →ₐ[k] k, toConv (b.comp φ) = ψ (toConv b)) :
    ∃ I : HopfIdeal k H, I.IsCentral ∧ I ≠ augmentation k H ∧ I.toIdeal.IsPrime := by
  refine ⟨vanishingIdeal ψ.range, (isCentral_vanishingIdeal_iff _).mpr hcenter,
    (vanishingIdeal_eq_augmentation_iff _).not.mpr hne, ?_⟩
  have hrange : (ψ.range : Set (WithConv (H →ₐ[k] k))) =
      Set.range fun b : H →ₐ[k] k ↦ toConv (b.comp φ) := by
    ext g
    simp only [MonoidHom.coe_range, Set.mem_range, hφ]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.ofConv, by rwa [toConv_ofConv]⟩, fun ⟨b, hb⟩ ↦ ⟨_, hb⟩⟩
  rw [vanishingIdeal_toIdeal_eq_ker φ ψ.range hrange, RingHom.ker_eq_comap_bot]
  -- A connected affine group over a perfect field is irreducible, so its zero ideal is prime.
  have hirreducible : IrreducibleSpace (PrimeSpectrum H) :=
    CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace k
      (_root_.CommHopfAlgCat.of k H)
  have hprime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirreducible
  rw [nilradical_eq_zero] at hprime
  exact hprime.comap φ

/-- A rational point `y` in the second centre but not in the centre gives a nontrivial
irreducible central closed subgroup: the closure of the commutators `⁅g, y⁆`. -/
private theorem exists_isCentral_isPrime_ne_augmentation_of_mem_upperCentralSeries_two
    {y : WithConv (H →ₐ[k] k)} (hy : y ∈ Subgroup.upperCentralSeries _ 2)
    (hyc : y ∉ Subgroup.center _) :
    ∃ I : HopfIdeal k H, I.IsCentral ∧ I ≠ augmentation k H ∧ I.toIdeal.IsPrime := by
  -- Commutators with `y` are central, so commutation with `y` is a homomorphism.
  have hcenter (g : WithConv (H →ₐ[k] k)) : ⁅g, y⁆ ∈ Subgroup.center _ := by
    rw [← Subgroup.upperCentralSeries_one, ← commutatorElement_inv]
    exact inv_mem (Subgroup.mem_upperCentralSeries_succ_iff.mp hy g)
  let ψ : WithConv (H →ₐ[k] k) →* WithConv (H →ₐ[k] k) :=
    { toFun g := ⁅g, y⁆
      map_one' := commutatorElement_one_left y
      map_mul' g g' := by
        rw [commutatorElement_mul_left_eq_conj_mul,
          Subgroup.mem_center_iff.mp (hcenter g') g, mul_inv_cancel_right]
        exact (Subgroup.mem_center_iff.mp (hcenter g') _).symm }
  refine exists_isCentral_isPrime_ne_augmentation_of_monoidHom ψ ?_ ?_
    ((Algebra.TensorProduct.productMap (AlgHom.id k H)
      ((Algebra.ofId k H).comp y.ofConv)).comp HopfAlgebra.commutatorAlgHom) fun b ↦ ?_
  · rintro _ ⟨g, rfl⟩
    exact hcenter g
  · -- A point not commuting with `y` has a nontrivial commutator with it.
    obtain ⟨g, hg⟩ : ∃ g, g * y ≠ y * g := by
      by_contra! h
      exact hyc (Subgroup.mem_center_iff.mpr h)
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨_, g, rfl⟩, fun h ↦ hg ?_⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h)
  · -- The coordinate map evaluates at `b` to the commutator of `b` with `y`.
    have hb : b.comp (Algebra.TensorProduct.productMap (AlgHom.id k H)
        ((Algebra.ofId k H).comp y.ofConv)) =
          Algebra.TensorProduct.productMap b y.ofConv := by
      ext x <;> simp
    rw [← AlgHom.comp_assoc, hb, HopfAlgebra.productMap_comp_commutatorAlgHom (toConv b) y,
      toConv_ofConv]
    rfl

/-- **A connected nilpotent group has a positive-dimensional centre.** A nontrivial reduced
connected finite-type affine group over an algebraically closed field whose group of rational
points is nilpotent has a nontrivial central closed subgroup with prime ideal, that is, a
nontrivial smooth connected central subgroup. -/
theorem exists_isCentral_isPrime_ne_augmentation_of_isNilpotent
    [Group.IsNilpotent (WithConv (H →ₐ[k] k))] [Nontrivial (WithConv (H →ₐ[k] k))] :
    ∃ I : HopfIdeal k H, I.IsCentral ∧ I ≠ augmentation k H ∧ I.toIdeal.IsPrime := by
  by_cases htop : Subgroup.center (WithConv (H →ₐ[k] k)) = ⊤
  · -- A commutative group of rational points: the whole group is central.
    have hrange : (MonoidHom.id (WithConv (H →ₐ[k] k))).range = ⊤ :=
      MonoidHom.range_eq_top.mpr Function.surjective_id
    refine exists_isCentral_isPrime_ne_augmentation_of_monoidHom (MonoidHom.id _) ?_ ?_
      (AlgHom.id k H) fun b ↦ rfl
    · rw [hrange, htop]
    · rw [hrange]
      exact top_ne_bot
  · -- Otherwise the second centre is strictly larger than the centre.
    have hlt : Subgroup.upperCentralSeries (WithConv (H →ₐ[k] k)) 1 <
        Subgroup.upperCentralSeries (WithConv (H →ₐ[k] k)) 2 := by
      refine lt_of_le_of_ne (Subgroup.upperCentralSeries_mono _ (by norm_num)) fun h ↦ htop ?_
      rw [← Subgroup.upperCentralSeries_one]
      exact Subgroup.upperCentralSeries.eq_top (by norm_num) h
    obtain ⟨y, hy, hyc⟩ := IsConcreteLE.exists_of_lt hlt
    rw [Subgroup.upperCentralSeries_one] at hyc
    exact exists_isCentral_isPrime_ne_augmentation_of_mem_upperCentralSeries_two hy hyc

/-- **A connected unipotent group has a positive-dimensional centre.** A nontrivial reduced
connected finite-type affine group over an algebraically closed field whose rational points are
all unipotent has a nontrivial central closed subgroup with prime ideal, that is, a nontrivial
smooth connected central subgroup. -/
theorem exists_isCentral_isPrime_ne_augmentation_of_forall_isUnipotentPoint
    [Nontrivial (WithConv (H →ₐ[k] k))]
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) :
    ∃ I : HopfIdeal k H, I.IsCentral ∧ I ≠ augmentation k H ∧ I.toIdeal.IsPrime := by
  have := HopfAlgebra.isNilpotent_points_of_forall_isUnipotentPoint_of_isAlgClosed hH
  exact exists_isCentral_isPrime_ne_augmentation_of_isNilpotent

end TauCeti.HopfIdeal
