/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Invariants
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.RepresentationTheory.Invariants

/-!
# The averaging contraction of the inhomogeneous cochains of a finite group

Let `G` be a finite group whose order is invertible in the commutative ring `k`, and let `A` be a
`k`-linear representation of `G`. Averaging an `(n + 1)`-cochain over its last argument,
$$(hf)(g_1, \dots, g_n) = \frac{1}{|G|} \sum_{g \in G} f(g_1, \dots, g_n, g),$$
is a contracting homotopy of the complex of inhomogeneous cochains `inhomogeneousCochains A`
in positive degrees, in Mathlib's convention for the differential
`inhomogeneousCochains.d`, whose first face is `g_0 • f(g_1, …, g_n)`. In degree `0` the same
operator recovers the averaging projection `Representation.averageMap` onto the invariants.

Precisely, with the sign `(-1)^(n+1)` on the component of degree `n + 1 → n`, the identity of
`inhomogeneousCochains A` is homotopic to the chain map that is `Representation.averageMap` in
degree `0` and zero in positive degrees, the projection onto the invariants placed in degree `0`.
In particular every positive-degree cocycle has an explicit primitive, `(-1)^(n+1)` times its
average over the last argument. The vanishing of positive-degree cohomology that this implies is
`groupCohomology.subsingleton_of_isUnit_natCard`, proved there by corestriction. The chain-level
contraction, rather than the vanishing alone, is what a comparison of cochain complexes built
from finite-group actions with their invariants uses.

The last argument is used because the last face of the differential, `f(g_0, …, g_{n-1})`, does
not involve the action, while the translation `g ↦ g_n g` absorbs the face that multiplies `g_n`
into the averaged variable.

## Main declarations

* `TauCeti.inhomogeneousCochains.averageLast`: the average of an `(n + 1)`-cochain over its last
  argument.
* `TauCeti.inhomogeneousCochains.d_comp_averageLast`: `h ∘ d = d ∘ h + (-1)^n` on
  `(n + 1)`-cochains.
* `TauCeti.inhomogeneousCochains.d_zero_comp_averageLast`: `h ∘ d = averageMap - 1` on
  `0`-cochains.
* `TauCeti.inhomogeneousCochains.d_smul_averageLast_of_d_eq_zero`: the explicit primitive of a
  positive-degree cocycle.
* `TauCeti.groupCohomology.averageCochainMap`: the averaging projection in degree `0`, as an
  endomorphism of `inhomogeneousCochains A`.
* `TauCeti.groupCohomology.averagingHomotopy`: the homotopy from the identity of
  `inhomogeneousCochains A` to `TauCeti.groupCohomology.averageCochainMap A`.

## References

* K. S. Brown, *Cohomology of groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter III, Sections 9 and 10, for the vanishing of positive-degree cohomology of a finite
  group whose order is invertible on the coefficients.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti.inhomogeneousCochains

open _root_.inhomogeneousCochains

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
variable (A : Rep k G)

/-- The average `x ↦ ⅟|G| • ∑ g, f (Fin.snoc x g)` of an `(n + 1)`-cochain `f` over its last
argument, an `n`-cochain. -/
def averageLast (n : ℕ) :
    ModuleCat.of k ((Fin (n + 1) → G) → A) ⟶ ModuleCat.of k ((Fin n → G) → A) :=
  ModuleCat.ofHom
  { toFun f x := ⅟(Fintype.card G : k) • ∑ g : G, f (Fin.snoc x g)
    map_add' f f' := by
      ext
      simp [Finset.sum_add_distrib]
    map_smul' r f := by
      ext
      simp [Finset.smul_sum, smul_comm r] }

/-- The value of the average over the last argument. -/
@[simp]
theorem averageLast_hom_apply (n : ℕ) (f : ModuleCat.of k ((Fin (n + 1) → G) → A))
    (x : Fin n → G) :
    (averageLast A n).hom f x = ⅟(Fintype.card G : k) • ∑ g : G, f (Fin.snoc x g) :=
  (rfl)

/-- **Averaging over the last argument is a homotopy relation with the differential.** On
`(n + 1)`-cochains, `h ∘ d = d ∘ h + (-1)^n`. -/
theorem d_comp_averageLast (n : ℕ) :
    d A (n + 1) ≫ averageLast A (n + 1) = averageLast A n ≫ d A n + (-1 : k) ^ n • 𝟙 _ := by
  ext f y
  -- Evaluate both sides at `f` and `y`: the right side becomes
  -- `ρ(y_0) (h f (tail y)) + ∑ j, (-1)^(j+1) • h f (contractNth j y) + (-1)^n • f y`.
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.add_apply, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply, d_hom_apply,
    Pi.add_apply, Pi.smul_apply]
  -- Unfold `h` and split the last two faces of `d f` evaluated at `Fin.snoc y g`. The other
  -- contractions commute with appending `g`; contracting the last two entries gives
  -- `f (Fin.snoc (init y) (y_n * g))`; the last face drops `g` and gives `f y`.
  simp only [averageLast, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk, d_hom_apply,
    Fin.snoc_apply_zero,
    Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n),
    Fin.contractNth_castSucc_castSucc_snoc,
    Fin.contractNth_castSucc_last_snoc, Fin.contractNth_last, Fin.init_snoc]
  -- The differential drops the first argument as `fun i => _ i.succ`, which is `Fin.tail`.
  have htail (g : G) : (fun i => (Fin.snoc y g : Fin (n + 2) → G) i.succ) =
      Fin.snoc (fun i => y i.succ) g :=
    Fin.tail_snoc y g
  have hlast : ∑ g, f (Fin.snoc (Fin.init y) (y (Fin.last n) * g)) =
      ∑ g, f (Fin.snoc (Fin.init y) g) :=
    Equiv.sum_comp (Equiv.mulLeft (y (Fin.last n))) fun g => f (Fin.snoc (Fin.init y) g)
  -- Distribute the sum over `G` across the faces and pull it past the action and the signs. The
  -- translation `hlast` absorbs `y_n` into the averaged variable, and the constant last face sums
  -- to `|G| • f y`. Both sides now match except for `⅟|G| • (-1)^(n+2) • |G| • f y` on the left.
  simp only [htail, Finset.sum_add_distrib, ← Finset.smul_sum, ← map_sum, hlast,
    Finset.sum_comm (γ := G), Finset.sum_const, Finset.card_univ, Fin.val_castSucc, Fin.val_last,
    smul_add, map_smul]
  -- Cancel `⅟|G|` against `|G|` and put the remaining scalars in a common position.
  have hc : ⅟(Fintype.card G : k) * ((-1) ^ (n + 1 + 1) * (Fintype.card G : k)) = (-1) ^ n := by
    rw [mul_left_comm, invOf_mul_self, mul_one]
    ring
  simp only [Finset.smul_sum, smul_smul, ← Nat.cast_smul_eq_nsmul k (Fintype.card G), hc,
    mul_comm (⅟(Fintype.card G : k))]
  abel

/-- **Averaging over the last argument of a coboundary of degree one.** On `0`-cochains,
`h ∘ d` is the averaging projection minus the identity. -/
theorem d_zero_comp_averageLast :
    d A 0 ≫ averageLast A 0 = ModuleCat.ofHom (A.ρ.averageMap.compLeft (Fin 0 → G)) - 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun y => ?_)
  have hy (z : Fin 0 → G) : z = y := Subsingleton.elim z y
  -- The sum of the constant `f y` over `G` is `|G| • f y`, which `⅟|G|` cancels.
  have hc : ⅟(Fintype.card G : k) • (Fintype.card G • f y) = f y := by
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]
  simp [averageLast, d_hom_apply, -Representation.averageMap, Representation.averageMap_apply, hy,
    Fin.snoc_zero, ← sub_eq_add_neg, Finset.sum_sub_distrib, smul_sub, hc]

/-- **The explicit primitive of a positive-degree cocycle.** An `(n + 1)`-cocycle `f` is the
coboundary of `(-1)^(n+1)` times its average over the last argument. -/
theorem d_smul_averageLast_of_d_eq_zero {n : ℕ} {f : ModuleCat.of k ((Fin (n + 1) → G) → A)}
    (hf : (d A (n + 1)).hom f = 0) :
    (d A n).hom ((-1 : k) ^ (n + 1) • (averageLast A n).hom f) = f := by
  have h := congr($(d_comp_averageLast A n).hom f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hf, map_zero, ModuleCat.hom_add,
    ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  have hsign : (-1 : k) ^ (n + 1) * (-1) ^ n = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨n, by ring⟩
  rw [map_smul, eq_neg_of_add_eq_zero_left h.symm, smul_neg, smul_smul, hsign, neg_one_smul,
    neg_neg]

end TauCeti.inhomogeneousCochains

namespace TauCeti.groupCohomology

open _root_.groupCohomology _root_.inhomogeneousCochains TauCeti.inhomogeneousCochains

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
variable (A : Rep k G)

/-- The averaging projection onto the invariants placed in degree `0`, as an endomorphism of the
complex of inhomogeneous cochains: it is `Representation.averageMap` on `0`-cochains and zero in
positive degrees. -/
def averageCochainMap : inhomogeneousCochains A ⟶ inhomogeneousCochains A where
  f
    | 0 => ModuleCat.ofHom (A.ρ.averageMap.compLeft (Fin 0 → G))
    | _ + 1 => 0
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rcases i with _ | i
    · rw [inhomogeneousCochains.d_def]
      refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun g => ?_)
      have hf (x : Fin 0 → G) : f x = f (Fin.contractNth 0 (· * ·) g) :=
        congrArg f (by subsingleton)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        _root_.inhomogeneousCochains.d_hom_apply, LinearMap.compLeft_apply, Function.comp_apply, hf,
        A.ρ.averageMap_invariant _ (g 0)]
      simp [Pi.zero_apply (M := fun _ => A)]
    · simp

/-- In degree `0`, `TauCeti.groupCohomology.averageCochainMap` is the averaging projection. -/
@[simp]
theorem averageCochainMap_f_zero :
    (averageCochainMap A).f 0 = ModuleCat.ofHom (A.ρ.averageMap.compLeft (Fin 0 → G)) :=
  (rfl)

/-- In positive degrees, `TauCeti.groupCohomology.averageCochainMap` is zero. -/
@[simp]
theorem averageCochainMap_f_succ (n : ℕ) : (averageCochainMap A).f (n + 1) = 0 :=
  (rfl)

/-- The components `(-1)^(j+1) • averageLast A j` of the averaging homotopy, from degree `j + 1`
to degree `j`. -/
private def averagingHomotopyHom (i j : ℕ) (hji : (ComplexShape.up ℕ).Rel j i) :
    (inhomogeneousCochains A).X i ⟶ (inhomogeneousCochains A).X j :=
  ((inhomogeneousCochains A).XIsoOfEq hji.symm).hom ≫ ((-1 : k) ^ (j + 1) • averageLast A j)

private theorem sub_averageCochainMap_eq_nullHomotopicMap' :
    𝟙 _ - averageCochainMap A = Homotopy.nullHomotopicMap' (averagingHomotopyHom A) := by
  ext n : 1
  rcases n with _ | n
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
      (show (ComplexShape.up ℕ).Rel 0 (0 + 1) from rfl) (fun l => by simp),
      inhomogeneousCochains.d_def]
    simp [averagingHomotopyHom, d_zero_comp_averageLast]
  · rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl),
      inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
    have hsign : (-1 : k) ^ (n + 1 + 1) * (-1) ^ n = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n + 1, by ring⟩
    have hneg : (-1 : k) ^ (n + 1 + 1) = -(-1) ^ (n + 1) := by rw [pow_succ, mul_neg_one]
    simp only [averagingHomotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, Linear.smul_comp, Linear.comp_smul, d_comp_averageLast, smul_add,
      smul_smul, hsign, one_smul, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply,
      averageCochainMap_f_succ, sub_zero]
    rw [hneg, neg_smul]
    abel

/-- **The averaging contraction.** The identity of the complex of inhomogeneous cochains is
homotopic to the averaging projection onto the invariants placed in degree `0`, through the
homotopy whose component from degree `n + 1` to degree `n` is `(-1)^(n+1)` times the average
over the last argument (`TauCeti.groupCohomology.averagingHomotopy_hom_succ`). -/
def averagingHomotopy : Homotopy (𝟙 (inhomogeneousCochains A)) (averageCochainMap A) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (sub_averageCochainMap_eq_nullHomotopicMap' A)).trans (Homotopy.nullHomotopy' _)

/-- The component of `TauCeti.groupCohomology.averagingHomotopy` from degree `n + 1` to degree
`n` is `(-1)^(n+1)` times the average over the last argument. -/
@[simp]
theorem averagingHomotopy_hom_succ (n : ℕ) :
    (averagingHomotopy A).hom (n + 1) n = (-1 : k) ^ (n + 1) • averageLast A n := by
  simp [averagingHomotopy, Homotopy.equivSubZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.nullHomotopy'_hom, averagingHomotopyHom]

end TauCeti.groupCohomology
