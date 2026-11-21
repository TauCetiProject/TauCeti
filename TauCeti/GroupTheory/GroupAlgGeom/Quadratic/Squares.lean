/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.BigPowers
public import TauCeti.GroupTheory.MalcevEquation
import TauCeti.GroupTheory.GroupAlgGeom.FreeDiscrimination
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.FreeProduct

/-!
# Radicals of products of two and three squares

Over a nonabelian fully residually free group, `x² y² = 1` has radical `ncl(x y)` and
`x² y² z² = 1` has radical the normal closure of `x y z` and the pairwise commutators. In the
alphabets of two and three variables, respectively, their coordinate groups are the free products
of the coefficient group with an infinite cyclic group and with a free abelian group of rank two.
The product relations are essential: commutation alone does not imply either equation.

The two-squares solution-set comparison needs only unique roots. The three-squares comparison
uses Vaught's condition and torsion-freeness. For the reverse radical inclusions, the quotients
by the stated relations are separated by the target group.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*,
  J. Algebra 200 (1998), §3, low-genus nonorientable forms.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*,
  J. Algebra 290 (2005), §2.7, Theorem 2 (4)–(5). The presentations here include the product
  relations missing from the printed formulas.
-/

public section

open Monoid.Coprod Subgroup Group
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G H X : Type*} [Group G] [Group H]

section TwoSquares

variable {x y : X} (hxy : x ≠ y)

/-- The quotient map imposing `x y = 1`. It substitutes `x⁻¹` for `y` and keeps every other
variable. -/
noncomputable def twoSquaresMap : GX G X →* GX G {w : X // w ≠ y} := by
  classical
  exact eval inl fun w => if hw : w ≠ y then inr (FreeGroup.of ⟨w, hw⟩)
    else (inr (FreeGroup.of ⟨x, hxy⟩))⁻¹

/-- The two-squares quotient map is evaluation at the substitution `y ↦ x⁻¹`. -/
theorem twoSquaresMap_def : twoSquaresMap (G := G) hxy = (by
    classical
    exact eval inl fun w => if hw : w ≠ y then inr (FreeGroup.of ⟨w, hw⟩)
      else (inr (FreeGroup.of ⟨x, hxy⟩))⁻¹) := (rfl)

/-- The two-squares quotient map fixes the coefficient homomorphism. -/
@[simp] theorem twoSquaresMap_comp_inl : (twoSquaresMap (G := G) hxy).comp inl = inl := by
  rw [twoSquaresMap_def, eval_comp_inl]

/-- The two-squares quotient map fixes each coefficient. -/
@[simp] theorem twoSquaresMap_inl (g : G) : twoSquaresMap hxy (inl g) = inl g :=
  DFunLike.congr_fun (twoSquaresMap_comp_inl hxy) g

/-- The eliminated variable maps to the inverse of `x`. -/
@[simp] theorem twoSquaresMap_inr_of_right : twoSquaresMap (G := G) hxy (inr (FreeGroup.of y)) =
    (inr (FreeGroup.of ⟨x, hxy⟩))⁻¹ := by
  simp [twoSquaresMap_def]

/-- Every other variable maps to its corresponding generator. -/
@[simp] theorem twoSquaresMap_inr_of_ne {w : X} (hw : w ≠ y) :
    twoSquaresMap (G := G) hxy (inr (FreeGroup.of w)) = inr (FreeGroup.of ⟨w, hw⟩) := by
  simp [twoSquaresMap_def, hw]

/-- The substitution onto the free group over the remaining alphabet is surjective. -/
theorem twoSquaresMap_surjective : Function.Surjective (twoSquaresMap (G := G) hxy) := by
  let j : GX G {w : X // w ≠ y} →* GX G X := eval inl fun w => inr (FreeGroup.of w.val)
  have hj : (twoSquaresMap hxy).comp j = .id _ :=
    GX.ext_hom (by intro g; simp [j]) (by intro w; simp [j, w.property])
  exact fun w => ⟨j w, DFunLike.congr_fun hj w⟩

/-- The kernel of the substitution is the normal closure of `x y`. -/
theorem ker_twoSquaresMap : (twoSquaresMap (G := G) hxy).ker =
    normalClosure {(inr (FreeGroup.of x) : GX G X) * inr (FreeGroup.of y)} := by
  let S : Set (GX G X) := {inr (FreeGroup.of x) * inr (FreeGroup.of y)}
  refine le_antisymm ?_ (normalClosure_le_normal (by simp [hxy]))
  let q := QuotientGroup.mk' (normalClosure S)
  let j := eval (q.comp inl) (fun w : {w : X // w ≠ y} => q (inr (FreeGroup.of w.val)))
  have hrel : q (inr (FreeGroup.of x) * inr (FreeGroup.of y)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (subset_normalClosure (Set.mem_singleton _))
  have hy : q (inr (FreeGroup.of y)) = (q (inr (FreeGroup.of x)))⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa using hrel)
  have hj : j.comp (twoSquaresMap hxy) = q := by
    apply GX.ext_hom
    · intro g; simp [j]
    · intro w
      by_cases hw : w = y
      · subst w; simp [j, hy]
      · simp [j, hw]
  intro w hw
  apply (QuotientGroup.eq_one_iff w).1
  exact (DFunLike.congr_fun hj w).symm.trans (by simp [MonoidHom.mem_ker.mp hw])

/-- With injective coefficients in a nonabelian CSA group with big powers, the radical
of `x² y² = 1` at distinct variables is the normal closure of `x y`. -/
theorem Rad_sq_mul_sq_eq_normalClosure {ι : G →* H} (hι : Function.Injective ι)
    (hBP : IsBP H) (hCSA : IsCSA H) (hH : ¬IsMulCommutative H) (hxy : x ≠ y) :
    Rad ι {(inr (FreeGroup.of x) : GX G X) ^ 2 * inr (FreeGroup.of y) ^ 2} =
      normalClosure {inr (FreeGroup.of x) * inr (FreeGroup.of y)} := by
  have := hBP.isMulTorsionFree
  have := hCSA.isCommTransitive.hasUniqueRoots
  let π : GHom (inl : G →* GX G X) (inl : G →* GX G {w : X // w ≠ y}) :=
    ⟨twoSquaresMap hxy, twoSquaresMap_inl hxy⟩
  have hd := GX.isDiscriminatedBy_of_injective (X := {w : X // w ≠ y}) ι hι hBP hCSA hH
  have hrad := hd.isSeparatedBy.Rad_ker_eq π
  -- The underlying homomorphism of `π` is the substitution whose kernel we computed.
  change Rad ι ↑(twoSquaresMap (G := G) hxy).ker = (twoSquaresMap hxy).ker at hrad
  rw [ker_twoSquaresMap, Rad_normalClosure] at hrad
  have hV : V ι {(inr (FreeGroup.of x) : GX G X) ^ 2 * inr (FreeGroup.of y) ^ 2} =
      V ι {inr (FreeGroup.of x) * inr (FreeGroup.of y)} := by
    ext v
    simp [mul_eq_one_iff_eq_inv, ← inv_pow, pow_left_inj two_ne_zero]
  rw [Rad_def, hV, ← Rad_def]
  exact hrad

end TwoSquares

/-- In a torsion-free Vaught group, the three-squares equation in arbitrary words is equivalent
to the product relation together with pairwise commutation. -/
theorem V_sq_mul_sq_mul_sq [IsMulTorsionFree H] (hV : IsVaught H) (ι : G →* H) (u w t : GX G X) :
    V ι {u ^ 2 * w ^ 2 * t ^ 2} = V ι {u * w * t, ⁅u, w⁆, ⁅u, t⁆, ⁅w, t⁆} := by
  ext v
  simp only [mem_V, Set.mem_singleton_iff, forall_eq, Set.mem_insert_iff,
    forall_eq_or_imp, map_mul, map_pow, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  constructor
  · intro h
    obtain ⟨hxy, hxz, hyz⟩ := (isVaught_iff H).mp hV _ _ _ h
    refine ⟨?_, hxy, hxz, hyz⟩
    apply (pow_eq_one_iff_left two_ne_zero).1
    rwa [(hxz.mul_left hyz).mul_pow, hxy.mul_pow]
  · rintro ⟨h, hxy, hxz, hyz⟩
    rw [← hxy.mul_pow, ← (hxz.mul_left hyz).mul_pow, h, one_pow]

section ThreeSquares

variable {x y z : X}

private abbrev ThreeSquaresBase (G : Type*) [Group G] :=
  Monoid.Coprod G (Fin 2 → Multiplicative ℤ)

private abbrev ThreeSquaresRest (x y z : X) := {w : X // w ≠ x ∧ w ≠ y ∧ w ≠ z}

/-- For distinct `x`, `y`, `z`, the quotient map imposing `x y z = 1` and pairwise commutation.
It sends `x` and `y` to the generators of a free abelian free factor, `z` to the inverse of their
product, and the other variables to free generators. For coincident variables, the first matching
assignment in the order `x`, `y`, `z` is used. -/
noncomputable def threeSquaresMap (G : Type*) [Group G] (x y z : X) :
    GX G X →* GX (Monoid.Coprod G (Fin 2 → Multiplicative ℤ)) {w : X // w ≠ x ∧ w ≠ y ∧ w ≠ z} := by
  classical
  exact eval (inl.comp inl) fun w =>
    let a (i : Fin 2) : Fin 2 → Multiplicative ℤ := Pi.mulSingle i (.ofAdd 1)
    if h : w ≠ x ∧ w ≠ y ∧ w ≠ z then inr (FreeGroup.of ⟨w, h⟩)
    else if w = x then inl (inr (a 0)) else if w = y then inl (inr (a 1))
    else (inl (inr (a 0)) * inl (inr (a 1)))⁻¹

/-- The three-squares quotient map is evaluation at the two abelian generators, their inverse
product, and the remaining free generators. -/
theorem threeSquaresMap_def : threeSquaresMap G x y z = (by
    classical
    exact eval (inl.comp inl) fun w =>
      let a (i : Fin 2) : Fin 2 → Multiplicative ℤ := Pi.mulSingle i (.ofAdd 1)
      if h : w ≠ x ∧ w ≠ y ∧ w ≠ z then inr (FreeGroup.of ⟨w, h⟩)
      else if w = x then inl (inr (a 0)) else if w = y then inl (inr (a 1))
      else (inl (inr (a 0)) * inl (inr (a 1)))⁻¹) := (rfl)

/-- The three-squares quotient map preserves the inclusion of the coefficients. -/
@[simp] theorem threeSquaresMap_comp_inl :
    (threeSquaresMap G x y z).comp inl = inl.comp inl := by
  rw [threeSquaresMap_def, eval_comp_inl]

/-- Each coefficient maps to its copy in the quotient. -/
@[simp] theorem threeSquaresMap_inl (g : G) : threeSquaresMap G x y z (inl g) = inl (inl g) :=
  DFunLike.congr_fun threeSquaresMap_comp_inl g

/-- The first variable maps to the first abelian generator. -/
@[simp] theorem threeSquaresMap_inr_of_left :
    threeSquaresMap G x y z (inr (FreeGroup.of x)) = inl (inr (Pi.mulSingle 0 (.ofAdd 1))) := by
  simp [threeSquaresMap_def]

/-- The second variable maps to the second abelian generator. -/
@[simp] theorem threeSquaresMap_inr_of_middle (hxy : x ≠ y) :
    threeSquaresMap G x y z (inr (FreeGroup.of y)) = inl (inr (Pi.mulSingle 1 (.ofAdd 1))) := by
  simp [threeSquaresMap_def, hxy.symm]

/-- The third variable maps to the inverse product of the two abelian generators. -/
@[simp] theorem threeSquaresMap_inr_of_right (hxz : x ≠ z) (hyz : y ≠ z) :
    threeSquaresMap G x y z (inr (FreeGroup.of z)) =
      (inl (inr (Pi.mulSingle 0 (.ofAdd 1))) * inl (inr (Pi.mulSingle 1 (.ofAdd 1))))⁻¹ := by
  simp [threeSquaresMap_def, hxz.symm, hyz.symm]

/-- Variables outside the equation map to the corresponding free generators. -/
@[simp] theorem threeSquaresMap_inr_of_ne {w : X} (hw : w ≠ x ∧ w ≠ y ∧ w ≠ z) :
    threeSquaresMap G x y z (inr (FreeGroup.of w)) = inr (FreeGroup.of ⟨w, hw⟩) := by
  simp [threeSquaresMap_def, hw]

/-- If the first two variables are distinct, the three-squares quotient map is surjective. -/
theorem threeSquaresMap_surjective (hxy : x ≠ y) :
    Function.Surjective (threeSquaresMap G x y z) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← GX.closure_image_inl_union_range_inr_of (G := ThreeSquaresBase G)
      (X := ThreeSquaresRest x y z)
      (T := ⊤) closure_univ, closure_le]
  rintro _ (⟨w, -, rfl⟩ | ⟨w, rfl⟩)
  · induction w using Monoid.Coprod.induction_on with
    | inl g => exact ⟨inl g, by simp⟩
    | inr v =>
      refine ⟨inr (FreeGroup.of x) ^ (v 0).toAdd * inr (FreeGroup.of y) ^ (v 1).toAdd, ?_⟩
      simp only [map_mul, map_zpow, threeSquaresMap_inr_of_left, threeSquaresMap_inr_of_middle hxy]
      let j : (Fin 2 → Multiplicative ℤ) →* GX (ThreeSquaresBase G) (ThreeSquaresRest x y z) :=
        inl.comp inr
      -- Combine the generator images using the inclusion of the abelian factor.
      change j _ ^ _ * j _ ^ _ = j v
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext i
      fin_cases i <;> simp
    | mul a b ha hb =>
      rw [map_mul]
      exact (threeSquaresMap G x y z).range.mul_mem ha hb
  · exact ⟨inr (FreeGroup.of w.val), threeSquaresMap_inr_of_ne w.property⟩

/-- The kernel is the normal closure of the product relation and the pairwise commutators. -/
theorem ker_threeSquaresMap (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (threeSquaresMap G x y z).ker = normalClosure
    {(inr (FreeGroup.of x) : GX G X) * inr (FreeGroup.of y) * inr (FreeGroup.of z),
      ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of y)⁆,
      ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of z)⁆,
      ⁅(inr (FreeGroup.of y) : GX G X), inr (FreeGroup.of z)⁆} := by
  let S : Set (GX G X) :=
    {inr (FreeGroup.of x) * inr (FreeGroup.of y) * inr (FreeGroup.of z),
      ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of y)⁆,
      ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of z)⁆,
      ⁅(inr (FreeGroup.of y) : GX G X), inr (FreeGroup.of z)⁆}
  have hS : normalClosure S ≤ (threeSquaresMap G x y z).ker := by
    apply normalClosure_le_normal
    simp only [S, Set.insert_subset_iff, Set.singleton_subset_iff]
    have hc (a b : Fin 2 → Multiplicative ℤ) : Commute
        (inl (inr a) : GX (ThreeSquaresBase G) (ThreeSquaresRest x y z)) (inl (inr b)) :=
      (Commute.all a b).map (inl.comp inr)
    simp [hxy, hxz, hyz, commutatorElement_eq_one_iff_commute, hc]
  let q := QuotientGroup.mk' (normalClosure S)
  have hc : Commute (q (inr (FreeGroup.of x))) (q (inr (FreeGroup.of y))) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).2 (subset_normalClosure (by simp [S]))
  let r : Fin 2 → GX G X ⧸ normalClosure S := ![q (inr (FreeGroup.of x)), q (inr (FreeGroup.of y))]
  have hr : ∀ i j, Commute (r i) (r j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [r, hc, hc.symm, Commute.refl]
  let j := eval (Monoid.Coprod.lift (q.comp inl) (zpowersPiHom r hr))
    (fun w : ThreeSquaresRest x y z => q (inr (FreeGroup.of w.val)))
  have hrel : q (inr (FreeGroup.of x) * inr (FreeGroup.of y) * inr (FreeGroup.of z)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (subset_normalClosure (by simp [S]))
  have hz : q (inr (FreeGroup.of z)) = (q (inr (FreeGroup.of x)) * q (inr (FreeGroup.of y)))⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa using hrel)
  have hj : j.comp (threeSquaresMap G x y z) = q := by
    apply GX.ext_hom
    · intro g; simp [j]
    · intro w
      by_cases wx : w = x
      · subst w; simp [j, r]
      by_cases wy : w = y
      · subst w; simp [j, r, hxy]
      by_cases wz : w = z
      · subst w; simp [j, r, hxz, hyz, hz]
      simp [j, threeSquaresMap_inr_of_ne ⟨wx, wy, wz⟩]
  refine le_antisymm (fun w hw => (QuotientGroup.eq_one_iff w).1 ?_) hS
  exact (DFunLike.congr_fun hj w).symm.trans (by simp [MonoidHom.mem_ker.mp hw])

/-- A free group over `G ∗ ℤ²` is discriminated over `G` by the nonabelian CSA BP target `H`. -/
private theorem threeSquaresTarget_isDiscriminatedBy {ι : G →* H} (hι : Function.Injective ι)
    (hBP : IsBP H) (hCSA : IsCSA H) (hH : ¬IsMulCommutative H) (Y : Type*) :
    IsDiscriminatedBy (inl.comp inl : G →* GX (ThreeSquaresBase G) Y) ι := by
  obtain ⟨u, v, huv⟩ : ∃ u v : H, ¬Commute u v := by
    simpa [isMulCommutative_iff, commute_iff_eq] using hH
  have hu : u ≠ 1 := by rintro rfl; exact huv (Commute.one_left _)
  have hv : v ∉ centralizer {u} := fun h => huv (mem_centralizer_singleton_iff.1 h).symm
  let f := LimitGroup.CentralizerExt.coprodPiLift u ι (MonoidHom.id (Fin 2 → Multiplicative ℤ)) v 0
  have hf : Function.Injective f := LimitGroup.CentralizerExt.coprodPiLift_injective 0
    hι Function.injective_id (hCSA.centralizer_isTISubgroup u) hv
  have hd := LimitGroup.CentralizerExt.isDiscriminatedBy (n := 2) hBP hCSA hu
  have hCSA' : IsCSA (LimitGroup.CentralizerExt u 2) := by
    classical
    refine hCSA.of_forall_exists_monoidHom fun a b ha hb => ?_
    obtain ⟨φ, hφ⟩ := (isDiscriminatedBy_def _ _).mp hd {a, b} (by simp [ha, hb])
    exact ⟨φ, hφ a (by simp), hφ b (by simp)⟩
  let j : H →* LimitGroup.CentralizerExt u 2 := LimitGroup.CentralizerExt.of
  have hna : ¬IsMulCommutative (LimitGroup.CentralizerExt u 2) := by
    intro h
    have hc : Commute (j u) (j v) := h.is_comm.comm _ _
    exact huv (hc.of_map (f := j) LimitGroup.CentralizerExt.of_injective)
  have hd' := (GX.isDiscriminatedBy_of_injective (X := Y) f hf (hBP.of_isDiscriminatedBy hd)
    hCSA' hna).comp (inl : G →* ThreeSquaresBase G)
  rw [show f.comp inl = j.comp ι from LimitGroup.CentralizerExt.coprodPiLift_comp_inl ..] at hd'
  exact hd'.trans (hd.comp ι)

/-- With injective coefficients in a nonabelian CSA BP group satisfying Vaught's condition,
the radical of `x² y² z² = 1` at distinct variables is the normal closure of `x y z` and the
three pairwise commutators. -/
theorem Rad_sq_mul_sq_mul_sq_eq_normalClosure {ι : G →* H} (hι : Function.Injective ι)
    (hBP : IsBP H) (hCSA : IsCSA H) (hV : IsVaught H) (hH : ¬IsMulCommutative H)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Rad ι {(inr (FreeGroup.of x) : GX G X) ^ 2 * inr (FreeGroup.of y) ^ 2 *
        inr (FreeGroup.of z) ^ 2} =
      normalClosure {inr (FreeGroup.of x) * inr (FreeGroup.of y) * inr (FreeGroup.of z),
        ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of y)⁆,
        ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of z)⁆,
        ⁅(inr (FreeGroup.of y) : GX G X), inr (FreeGroup.of z)⁆} := by
  have := hBP.isMulTorsionFree
  let π : GHom (inl : G →* GX G X)
      (inl.comp inl : G →* GX (ThreeSquaresBase G) (ThreeSquaresRest x y z)) :=
    ⟨threeSquaresMap G x y z, threeSquaresMap_inl⟩
  have hd := threeSquaresTarget_isDiscriminatedBy hι hBP hCSA hH (ThreeSquaresRest x y z)
  have hrad := hd.isSeparatedBy.Rad_ker_eq π
  -- The underlying homomorphism of `π` is `threeSquaresMap`.
  change Rad ι ↑(threeSquaresMap G x y z).ker = (threeSquaresMap G x y z).ker at hrad
  rw [ker_threeSquaresMap hxy hxz hyz, Rad_normalClosure] at hrad
  rw [Rad_def, V_sq_mul_sq_mul_sq hV, ← Rad_def]
  exact hrad

end ThreeSquares

namespace Standard

/-- The radical of the coefficient-free standard equation of nonorientable genus two is the
normal closure of the product of its two variables. -/
theorem Rad_toWord_nonorientable_two {ι : G →* H} (hι : Function.Injective ι)
    (hBP : IsBP H) (hCSA : IsCSA H) (hH : ¬IsMulCommutative H) {x : Fin 2 → X} (hx : x.Injective) :
    Rad ι {(nonorientable (G := G) 2 (by decide) x hx).toWord} =
      normalClosure {(inr (FreeGroup.of (x 0)) : GX G X) * inr (FreeGroup.of (x 1))} := by
  simpa [toWord_def, List.ofFn_succ] using
    Rad_sq_mul_sq_eq_normalClosure hι hBP hCSA hH (hx.ne (by decide : (0 : Fin 2) ≠ 1))

/-- The radical of the coefficient-free standard equation of nonorientable genus three is the
normal closure of the product of its three variables and their pairwise commutators. -/
theorem Rad_toWord_nonorientable_three {ι : G →* H} (hι : Function.Injective ι)
    (hBP : IsBP H) (hCSA : IsCSA H) (hV : IsVaught H) (hH : ¬IsMulCommutative H)
    {x : Fin 3 → X} (hx : x.Injective) :
    Rad ι {(nonorientable (G := G) 3 (by decide) x hx).toWord} =
      normalClosure
        {(inr (FreeGroup.of (x 0)) : GX G X) * inr (FreeGroup.of (x 1)) * inr (FreeGroup.of (x 2)),
          ⁅(inr (FreeGroup.of (x 0)) : GX G X), inr (FreeGroup.of (x 1))⁆,
          ⁅(inr (FreeGroup.of (x 0)) : GX G X), inr (FreeGroup.of (x 2))⁆,
          ⁅(inr (FreeGroup.of (x 1)) : GX G X), inr (FreeGroup.of (x 2))⁆} := by
  simpa [toWord_def, List.ofFn_succ, mul_assoc] using
    Rad_sq_mul_sq_mul_sq_eq_normalClosure hι hBP hCSA hV hH (hx.ne (by decide : (0 : Fin 3) ≠ 1))
      (hx.ne (by decide : (0 : Fin 3) ≠ 2)) (hx.ne (by decide : (1 : Fin 3) ≠ 2))

end Standard

/-- Pairwise commutation alone does not impose the three-squares equation. In particular,
the product relation cannot be dropped from its radical presentation. -/
theorem sq_mul_sq_mul_sq_notMem_normalClosure_commutators (x y z : X) :
    (inr (FreeGroup.of x) : GX G X) ^ 2 * inr (FreeGroup.of y) ^ 2 *
        inr (FreeGroup.of z) ^ 2 ∉ normalClosure
      {⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of y)⁆,
        ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of z)⁆,
        ⁅(inr (FreeGroup.of y) : GX G X), inr (FreeGroup.of z)⁆} := by
  let f := eval (1 : G →* Multiplicative ℤ) (fun _ : X => Multiplicative.ofAdd 1)
  have hker : normalClosure
      {⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of y)⁆,
        ⁅(inr (FreeGroup.of x) : GX G X), inr (FreeGroup.of z)⁆,
        ⁅(inr (FreeGroup.of y) : GX G X), inr (FreeGroup.of z)⁆} ≤ f.ker := by
    apply normalClosure_le_normal
    simp [Set.subset_def, commutatorElement_eq_one_iff_commute, Commute.all]
  intro h
  have heq := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp (hker h))
  norm_num [f] at heq

end TauCeti.GroupAlgGeom.Quadratic
