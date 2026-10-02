/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.Quotient

/-!
# Levi complements of abelian ideals

Let `L` be a finite-dimensional Lie algebra over a field of characteristic zero and `I` an ideal of
`L` whose quotient `L ⧸ I` has nondegenerate Killing form. This file proves that `I` has a
complementary Lie subalgebra whenever `I` is abelian
(`LieIdeal.exists_lieSubalgebra_isCompl_of_isLieAbelian`), and a complementary ideal whenever `I`
is central (`LieIdeal.exists_isCompl_of_le_center`).

These are the base cases of Levi's theorem. Its proof by induction on the dimension reduces to
the case where the solvable radical `R` contains no nonzero proper ideal of `L`. Such an `R` is
abelian, since its derived algebra is a proper ideal of `L` contained in `R`, and it is either
central or meets the centre trivially.

## The argument

A central ideal `I` is a Lie submodule of the adjoint module, on which `I` acts trivially, so Weyl's
theorem for the action of `L ⧸ I` (`LieSubmodule.exists_isCompl_of_le_ker`) complements it by a
submodule, that is, by an ideal.

For an abelian ideal `I`, let `L` act on its endomorphisms by commutators with the adjoint action,
and consider the submodules

* `C`, the endomorphisms with range in `I` that act on `I` as a scalar;
* `B ≤ C`, those that vanish on `I`;
* `A ≤ B`, the inner derivations `ad a` by elements `a ∈ I`.

The algebra `L` carries `C` into `B`, and `I` carries `C` into `A`: for `r ∈ I` and `φ ∈ C` acting
on `I` as `c`, the bracket `⁅r, φ⁆` is `ad (-(c • r))`. So `L ⧸ I` acts on `C / A`, and Weyl's
theorem complements `B / A` in `C / A`; when `I ≠ 0`, the complement is nonzero, and as `L` carries
it into `B / A` it consists of invariants. Rescaling a nonzero invariant gives a projection `ψ` of
`L` onto `I` with `⁅x, ψ⁆ ∈ A` for every `x : L`. Its stabilizer `S = {x | ⁅x, ψ⁆ = 0}` is a Lie
subalgebra with `I + S = L`, and `S ∩ I` consists of central elements.

If `I` meets the centre trivially, `S` is already the complement; this is the classical argument.
In general `S ∩ I` is a central ideal of `S` with quotient `L ⧸ I`, so the central case complements
it inside `S`, and that complement is a complement of `I` in `L`.

## Main results

* `LieIdeal.exists_isCompl_of_le_center`: a central ideal with Killing quotient has a
  complementary ideal.
* `LieIdeal.exists_lieSubalgebra_isCompl_of_isLieAbelian`: an abelian ideal with Killing quotient
  has a complementary Lie subalgebra.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129, Appendix E,
  for the proof of Levi's theorem by reduction to a minimal abelian ideal, and the submodules
  `A ≤ B ≤ C` used for an ideal meeting the centre trivially.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]

/-- **A central ideal is a direct summand** when the quotient by it has nondegenerate Killing form:
it has a complementary ideal. -/
theorem _root_.LieIdeal.exists_isCompl_of_le_center [CharZero K] [FiniteDimensional K L]
    (I : LieIdeal K L) [IsKilling K (L ⧸ I)] (hI : I ≤ center K L) :
    ∃ J : LieIdeal K L, IsCompl I J :=
  LieSubmodule.exists_isCompl_of_le_ker I (hI.trans (self_module_ker_eq_center K L).ge)

section Abelian

variable (I : LieIdeal K L)

/-- `L` carries an endomorphism with range in `I`, acting on `I` as a scalar, to one with range in
`I` vanishing on `I`. -/
private theorem lie_apply_mem_and_lie_apply_eq_zero {φ : L →ₗ[K] L} (hφ : ∀ y, φ y ∈ I) {c : K}
    (hc : ∀ r ∈ I, φ r = c • r) (x : L) : (∀ y, ⁅x, φ⁆ y ∈ I) ∧ ∀ r ∈ I, ⁅x, φ⁆ r = 0 := by
  refine ⟨fun y ↦ ?_, fun r hr ↦ ?_⟩
  · rw [LieHom.lie_apply]
    exact sub_mem (I.lie_mem (hφ y)) (hφ _)
  · rw [LieHom.lie_apply, hc r hr, hc _ (I.lie_mem hr), lie_smul, sub_self]

/-- The endomorphisms of `L` with range in `I` that vanish on `I`. -/
private def zeroOnIdeal : LieSubmodule K L (L →ₗ[K] L) where
  carrier := {φ | (∀ y, φ y ∈ I) ∧ ∀ r ∈ I, φ r = 0}
  add_mem' := by
    rintro φ ψ ⟨hφ, hφ'⟩ ⟨hψ, hψ'⟩
    exact ⟨fun y ↦ add_mem (hφ y) (hψ y), fun r hr ↦ by
      rw [LinearMap.add_apply, hφ' r hr, hψ' r hr, add_zero]⟩
  zero_mem' := ⟨fun _ ↦ zero_mem _, fun _ _ ↦ LinearMap.zero_apply _⟩
  smul_mem' := by
    rintro a φ ⟨hφ, hφ'⟩
    exact ⟨fun y ↦ I.smul_mem a (hφ y), fun r hr ↦ by
      rw [LinearMap.smul_apply, hφ' r hr, smul_zero]⟩
  lie_mem := by
    rintro x φ ⟨hφ, hφ'⟩
    exact lie_apply_mem_and_lie_apply_eq_zero I hφ (c := 0)
      (fun r hr ↦ by rw [hφ' r hr, zero_smul]) x

/-- The endomorphisms of `L` with range in `I` that act on `I` as a scalar. -/
private def scalarOnIdeal : LieSubmodule K L (L →ₗ[K] L) where
  carrier := {φ | (∀ y, φ y ∈ I) ∧ ∃ c : K, ∀ r ∈ I, φ r = c • r}
  add_mem' := by
    rintro φ ψ ⟨hφ, c, hc⟩ ⟨hψ, d, hd⟩
    exact ⟨fun y ↦ add_mem (hφ y) (hψ y), c + d, fun r hr ↦ by
      rw [LinearMap.add_apply, hc r hr, hd r hr, add_smul]⟩
  zero_mem' := ⟨fun _ ↦ zero_mem _, 0, fun r _ ↦ by rw [LinearMap.zero_apply, zero_smul]⟩
  smul_mem' := by
    rintro a φ ⟨hφ, c, hc⟩
    exact ⟨fun y ↦ I.smul_mem a (hφ y), a * c, fun r hr ↦ by
      rw [LinearMap.smul_apply, hc r hr, mul_smul]⟩
  lie_mem := by
    rintro x φ ⟨hφ, c, hc⟩
    obtain ⟨h, h'⟩ := lie_apply_mem_and_lie_apply_eq_zero I hφ hc x
    exact ⟨h, 0, fun r hr ↦ by rw [h' r hr, zero_smul]⟩

/-- The inner derivations of `L` by elements of `I`. -/
private def adOfIdeal : LieSubmodule K L (L →ₗ[K] L) where
  carrier := {φ | ∃ a ∈ I, ad K L a = φ}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨c • a, I.smul_mem c ha, map_smul _ _ _⟩
  lie_mem := by
    rintro x _ ⟨a, ha, rfl⟩
    refine ⟨⁅x, a⁆, I.lie_mem ha, LinearMap.ext fun y ↦ ?_⟩
    rw [LieHom.lie_apply, ad_apply, ad_apply, ad_apply, lie_lie]

variable {I}

/-- Two elements of an abelian ideal commute. -/
private theorem lie_eq_zero_of_mem [IsLieAbelian I] {a r : L} (ha : a ∈ I) (hr : r ∈ I) :
    ⁅a, r⁆ = 0 :=
  congr_arg Subtype.val (trivial_lie_zero I I ⟨a, ha⟩ ⟨r, hr⟩)

/-- An element `r` of an abelian ideal `I` acts on an endomorphism with range in `I`, acting on
`I` as the scalar `c`, as the inner derivation `-ad (c • r)`. -/
private theorem lie_eq_ad_of_mem [IsLieAbelian I] {φ : L →ₗ[K] L} (hφ : ∀ y, φ y ∈ I) {c : K}
    (hc : ∀ r ∈ I, φ r = c • r) {r : L} (hr : r ∈ I) : ⁅r, φ⁆ = ad K L (-(c • r)) := by
  ext y
  rw [LieHom.lie_apply, hc _ (lie_mem_left K L I r y hr), ad_apply, neg_lie, smul_lie,
    lie_eq_zero_of_mem hr (hφ y), zero_sub]

/-- For an abelian ideal `I` with Killing quotient, there is a projection `ψ` of `L` onto `I`
whose bracket with every element of `L` is an inner derivation by an element of `I`. -/
private theorem exists_projection [CharZero K] [FiniteDimensional K L] [IsLieAbelian I]
    [IsKilling K (L ⧸ I)] (hI : I ≠ ⊥) :
    ∃ ψ : L →ₗ[K] L, (∀ y, ψ y ∈ I) ∧ (∀ r ∈ I, ψ r = r) ∧ ∀ x : L, ⁅x, ψ⁆ ∈ adOfIdeal I := by
  let C := scalarOnIdeal I
  let A := (adOfIdeal I).comap C.incl
  let B := ((zeroOnIdeal I).comap C.incl).map (LieSubmodule.Quotient.mk' A)
  -- `L` carries `C` into `B`, and `I` carries `C` into `A`.
  have hLB (x : L) (φ : C) : ⁅x, LieSubmodule.Quotient.mk' A φ⁆ ∈ B := by
    obtain ⟨hφ, c, hc⟩ := φ.2
    rw [← LieModuleHom.map_lie]
    refine LieSubmodule.mem_map_of_mem ?_
    rw [LieSubmodule.mem_comap, LieSubmodule.incl_apply, LieSubmodule.coe_bracket]
    exact lie_apply_mem_and_lie_apply_eq_zero I hφ hc x
  have hker : I ≤ LieModule.ker K L (C ⧸ A) := by
    intro r hr
    rw [LieModule.mem_ker]
    intro q
    obtain ⟨φ, rfl⟩ := LieSubmodule.Quotient.surjective_mk' A q
    obtain ⟨hφ, c, hc⟩ := φ.2
    rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk'_apply,
      LieSubmodule.Quotient.mk_eq_zero', LieSubmodule.mem_comap, LieSubmodule.incl_apply,
      LieSubmodule.coe_bracket, lie_eq_ad_of_mem hφ hc hr]
    exact ⟨_, I.neg_mem (I.smul_mem c hr), rfl⟩
  obtain ⟨D, hD⟩ := B.exists_isCompl_of_le_ker hker
  -- A projection of `L` onto `I` lies in `C` but not in `B`, so `B` is proper.
  have hBtop : B ≠ ⊤ := by
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl I.toSubmodule
    obtain ⟨r₀, hr₀, hr₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      ((LieSubmodule.toSubmodule_eq_bot I).not.mpr hI)
    let φ₀ : L →ₗ[K] L := I.toSubmodule.projection W hW
    have hφ₀ (r : L) (hr : r ∈ I) : φ₀ r = r := Submodule.projection_apply_of_mem_left hW hr
    have hφ₀C : φ₀ ∈ C := ⟨Submodule.projection_apply_mem hW, 1,
      fun r hr ↦ by rw [hφ₀ r hr, one_smul]⟩
    intro htop
    obtain ⟨β, ⟨-, hβ⟩, hβφ₀⟩ := (LieSubmodule.mem_map _).1 (htop ▸ LieSubmodule.mem_top
      (LieSubmodule.Quotient.mk' A ⟨φ₀, hφ₀C⟩))
    rw [← sub_eq_zero, ← map_sub, LieSubmodule.Quotient.mk_eq_zero, LieSubmodule.mem_comap,
      LieSubmodule.incl_apply] at hβφ₀
    obtain ⟨a, ha, hadβ⟩ := hβφ₀
    have hβr₀ : (β : L →ₗ[K] L) r₀ = 0 := hβ r₀ hr₀
    have h := LinearMap.congr_fun hadβ r₀
    rw [ad_apply, lie_eq_zero_of_mem ha hr₀, LieSubmodule.coe_sub, LinearMap.sub_apply, hβr₀,
      hφ₀ r₀ hr₀, zero_sub, zero_eq_neg] at h
    exact hr₀0 h
  -- A nonzero vector of the complement `D` is invariant and lies outside `B`.
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((LieSubmodule.toSubmodule_eq_bot D).not.mpr fun h ↦ hBtop (eq_top_of_isCompl_bot (h ▸ hD)))
  obtain ⟨φ, rfl⟩ := LieSubmodule.Quotient.surjective_mk' A v
  have hBD {q} (hqB : q ∈ B) (hqD : q ∈ D) : q = 0 := by
    rw [← LieSubmodule.mem_bot (R := K) (L := L), ← hD.inf_eq_bot]
    exact ⟨hqB, hqD⟩
  obtain ⟨hφ, c, hc⟩ := φ.2
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine hv0 (hBD (LieSubmodule.mem_map_of_mem ?_) hv)
    rw [LieSubmodule.mem_comap, LieSubmodule.incl_apply]
    exact ⟨hφ, fun r hr ↦ by rw [hc r hr, zero_smul]⟩
  refine ⟨c⁻¹ • (φ : L →ₗ[K] L), fun y ↦ I.smul_mem _ (hφ y),
    fun r hr ↦ by rw [LinearMap.smul_apply, hc r hr, inv_smul_smul₀ hc0], fun x ↦ ?_⟩
  have hx := hBD (hLB x φ) (D.lie_mem hv)
  rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, LieSubmodule.mem_comap,
    LieSubmodule.incl_apply, LieSubmodule.coe_bracket] at hx
  rw [lie_smul]
  exact (adOfIdeal I).smul_mem _ hx

/-- An abelian ideal `I` with Killing quotient has a supplement `S`, a Lie subalgebra with
`I + S = L`, meeting `I` only in central elements: the stabilizer of the projection of
`exists_projection`. -/
private theorem exists_lieSubalgebra_codisjoint [CharZero K] [FiniteDimensional K L]
    [IsLieAbelian I] [IsKilling K (L ⧸ I)] :
    ∃ S : LieSubalgebra K L, Codisjoint I.toSubmodule S.toSubmodule ∧
      ∀ x ∈ S, x ∈ I → x ∈ center K L := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · refine ⟨⊤, by rw [LieSubalgebra.top_toSubmodule]; exact codisjoint_top_right, fun x _ hx ↦ ?_⟩
    rw [(LieSubmodule.mem_bot x).1 hx]
    exact zero_mem _
  obtain ⟨ψ, hψI, hψ, hψA⟩ := exists_projection hI
  have hψr {r : L} (hr : r ∈ I) : ⁅r, ψ⁆ = -ad K L r := by
    rw [lie_eq_ad_of_mem hψI (c := 1) (fun r hr ↦ by rw [hψ r hr, one_smul]) hr, one_smul,
      map_neg]
  let S : LieSubalgebra K L :=
    { carrier := {x | ⁅x, ψ⁆ = 0}
      add_mem' := fun {x y} hx hy ↦ by
        rw [Set.mem_ofPred_eq] at hx hy ⊢
        rw [add_lie, hx, hy, add_zero]
      zero_mem' := zero_lie ψ
      smul_mem' := fun c x hx ↦ by
        rw [Set.mem_ofPred_eq] at hx ⊢
        rw [smul_lie, hx, smul_zero]
      lie_mem' := fun {x y} hx hy ↦ by
        rw [Set.mem_ofPred_eq] at hx hy ⊢
        rw [lie_lie, hx, hy, lie_zero, lie_zero, sub_zero] }
  have hS (x : L) : x ∈ S ↔ ⁅x, ψ⁆ = 0 := LieSubalgebra.mem_mk_iff _ _ _ _ _
  refine ⟨S, codisjoint_iff.2 (Submodule.eq_top_iff'.2 fun x ↦ ?_), fun x hxS hxI ↦ ?_⟩
  · obtain ⟨a, ha, hax⟩ := hψA x
    refine Submodule.mem_sup.2 ⟨-a, I.neg_mem ha, x + a, (hS _).2 ?_, ?_⟩
    · rw [add_lie, ← hax, hψr ha, add_neg_cancel]
    · rw [add_comm x a, neg_add_cancel_left]
  · have hx := (hS x).1 hxS
    rw [hψr hxI, neg_eq_zero, ← LieHom.mem_ker, ad_ker_eq_self_module_ker,
      self_module_ker_eq_center] at hx
    exact hx

end Abelian

/-- **A Levi complement of an abelian ideal.** Over a field of characteristic zero, an abelian
ideal `I` of a finite-dimensional Lie algebra `L` whose quotient `L ⧸ I` has nondegenerate Killing
form has a complementary Lie subalgebra. -/
theorem _root_.LieIdeal.exists_lieSubalgebra_isCompl_of_isLieAbelian [CharZero K]
    [FiniteDimensional K L] (I : LieIdeal K L) [IsLieAbelian I] [IsKilling K (L ⧸ I)] :
    ∃ S : LieSubalgebra K L, IsCompl I.toSubmodule S.toSubmodule := by
  obtain ⟨S, hIS, hSI⟩ := exists_lieSubalgebra_codisjoint (I := I)
  -- The ideal `S ∩ I` of `S` is central, with quotient `L ⧸ I`, so it has a complement in `S`.
  let g : S →ₗ⁅K⁆ L ⧸ I := I.mkQ.comp S.incl
  have hg (x : S) : x ∈ g.ker ↔ (x : L) ∈ I := by
    rw [LieHom.mem_ker, LieHom.comp_apply, LieSubalgebra.coe_incl, LieIdeal.mkQ_apply,
      LieSubmodule.Quotient.mk_eq_zero']
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := I.mkQ_surjective y
    obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.1 (hIS.eq_top ▸ Submodule.mem_top (x := x))
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [LieHom.comp_apply, LieSubalgebra.coe_incl, ← sub_eq_zero, ← map_sub, ← LieHom.mem_ker,
      LieIdeal.ker_mkQ, Subtype.coe_mk, sub_add_cancel_right]
    exact I.neg_mem hi
  have : IsKilling K (S ⧸ g.ker) := isKilling_of_equiv (LieEquiv.ofBijective (g.ker.liftQ g le_rfl)
    ⟨g.ker.liftQ_injective g le_rfl le_rfl, g.ker.liftQ_surjective g le_rfl hgs⟩).symm
  obtain ⟨J, hJ⟩ := g.ker.exists_isCompl_of_le_center fun x hx ↦ by
    have hx := hSI x x.2 ((hg x).1 hx)
    rw [← self_module_ker_eq_center, LieModule.mem_ker] at hx ⊢
    intro y
    ext
    rw [LieSubalgebra.coe_bracket, hx, ZeroMemClass.coe_zero]
  rw [← LieSubmodule.isCompl_toSubmodule] at hJ
  -- The complement of `S ∩ I` in `S` is a complement of `I` in `L`.
  refine ⟨(J : LieSubalgebra K S).map S.incl, ⟨Submodule.disjoint_def.2 fun x hxI hxJ ↦ ?_,
    codisjoint_iff.2 (Submodule.eq_top_iff'.2 fun x ↦ ?_)⟩⟩
  · obtain ⟨j, hj, rfl⟩ := (LieSubalgebra.mem_map ..).1 hxJ
    rw [LieSubalgebra.coe_incl] at hxI ⊢
    rw [Submodule.disjoint_def.1 hJ.disjoint j ((hg j).2 hxI) hj, ZeroMemClass.coe_zero]
  · obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.1 (hIS.eq_top ▸ Submodule.mem_top (x := x))
    obtain ⟨k, hk, j, hj, hkj⟩ := Submodule.mem_sup.1
      (hJ.codisjoint.eq_top ▸ Submodule.mem_top (x := (⟨s, hs⟩ : S)))
    refine Submodule.mem_sup.2 ⟨i + k, I.add_mem hi ((hg k).1 hk), j,
      (LieSubalgebra.mem_map ..).2 ⟨j, hj, rfl⟩, ?_⟩
    rw [add_assoc, ← AddMemClass.coe_add, hkj]

end TauCeti
