/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Data.ZMod.Defs
public import TauCeti.GroupTheory.GroupAlgGeom.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Concept

/-!
# Algebraic sets, radicals and coordinate groups over a group

Let `H` be a group receiving the coefficients `G` through `ι : G →* H`. A system of equations
over `G` in the variables `X` is a subset `S ⊆ G[X]`, and its solutions in `H` form the
*algebraic set* `V_H(S) ⊆ H^X`. Conversely the equations vanishing on a set of points
`Y ⊆ H^X` form a normal subgroup `I_H(Y)` of `G[X]`, the *ideal* of `Y`. These two operations are
the upper and lower polars of the relation `eval ι v s = 1`, so they form an antitone Galois
connection. The *radical* `Rad_H(S) = I_H(V_H(S))` of `S` is the largest
system with the same solutions as `S`; it contains the normal closure of `S`, generally strictly.

A `G`-homomorphism from a quotient `G[X] ⧸ N` to `H` is the same as a point of `H^X` at which
every equation of `N` vanishes. Quotienting `G[X]` by the radical gives the *coordinate group*
`G_{R(S)}` of `S`, while quotienting by the normal closure gives the group `G_S` presented by the
system itself; there is a surjection `G_S →* G_{R(S)}` compatible with the coefficients. When `ι`
is injective and `S` has a solution in `H`, both coefficient maps are injective, so `G_{R(S)}` is a
`G`-group.

The radical genuinely depends on the group `H` in which the solutions are taken, and differs from
the normal closure: over a torsion-free `H` with injective coefficients, the radical of the
one-variable system `x ^ n = 1` (`n ≠ 0`) is the normal closure of `x`, which does not lie in the
normal closure of `x ^ n` when `n ≠ 1`.

## Main definitions

* `TauCeti.GroupAlgGeom.V ι S`: the algebraic set `V_H(S)` of a system `S ⊆ G[X]`.
* `TauCeti.GroupAlgGeom.I ι Y`: the ideal `I_H(Y)`, a normal subgroup of `G[X]`.
* `TauCeti.GroupAlgGeom.Rad ι S`: the radical `Rad_H(S) = I_H(V_H(S))`.
* `TauCeti.GroupAlgGeom.CoordGroup ι S`: the coordinate group `G_{R(S)} = G[X] ⧸ Rad_H(S)`.
* `TauCeti.GroupAlgGeom.SystemGroup G S`: the group `G_S = G[X] ⧸ ncl(S)` of the system `S`.
* `TauCeti.GroupAlgGeom.SystemGroup.toCoordGroup ι S`: the surjection `G_S →* G_{R(S)}`.

## Main results

* `TauCeti.GroupAlgGeom.galoisConnection_V_I`: `V` and `I` form an antitone Galois connection.
* `TauCeti.GroupAlgGeom.V_normalClosure`, `TauCeti.GroupAlgGeom.normalClosure_le_Rad`: a system
  and its normal closure have the same solutions, so `ncl(S) ≤ Rad_H(S)`.
* `TauCeti.GroupAlgGeom.V_I_V`: `V(I(V(S))) = V(S)`.
* `TauCeti.GroupAlgGeom.preimage_wordMap_V`: inverse images of algebraic sets under word maps
  are algebraic.
* `TauCeti.GroupAlgGeom.exists_finite_V_eq_of_finite`,
  `TauCeti.GroupAlgGeom.exists_subsingleton_V_eq`: with finitely many points, every system has a
  finite subsystem with the same solutions; with at most one point, for instance with no
  variables, a single equation suffices.
* `TauCeti.GroupAlgGeom.I_singleton_comp`: the ideal of a point with coordinates `ι (g x)` is the
  normal closure of the equations `x (g x)⁻¹`, for injective `ι`.
* `TauCeti.GroupAlgGeom.GX.quotientHomEquiv`: `G`-homomorphisms from `G[X] ⧸ N` to `H`
  correspond to the points of `V_H(N)`.
* `TauCeti.GroupAlgGeom.CoordGroup.homEquiv`, `TauCeti.GroupAlgGeom.SystemGroup.homEquiv`:
  `G`-homomorphisms from `G_{R(S)}` or from `G_S` to `H` correspond to the solutions of `S` in `H`.
* `TauCeti.GroupAlgGeom.CoordGroup.coeff_injective`: `G_{R(S)}` is a `G`-group when `S` has a
  solution in a `G`-group.
* `TauCeti.GroupAlgGeom.Rad_pow_eq_normalClosure`,
  `TauCeti.GroupAlgGeom.normalClosure_pow_ne_normalClosure`: over a torsion-free `H` with
  injective coefficients, the radical of `x ^ n` (`n ≠ 0`) is the normal closure of `x`, which
  strictly contains that of `x ^ n` when `n ≠ 1`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §1 and §§3.1–3.4.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.4.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup

variable {G H X : Type*} [Group G] [Group H]

variable (ι : G →* H)

/-! ### Algebraic sets and ideals -/

/-- The algebraic set `V_H(S) ⊆ H^X` of a system of equations `S ⊆ G[X]`: the points `v : X → H`
at which every equation of `S` evaluates to `1`. -/
def V (S : Set (GX G X)) : Set (X → H) :=
  upperPolar (fun s v => eval ι v s = 1) S

/-- The ideal `I_H(Y)` of a set of points `Y ⊆ H^X`: the equations of `G[X]` vanishing at every
point of `Y`. It is a normal subgroup of `G[X]`. -/
def I (Y : Set (X → H)) : Subgroup (GX G X) where
  carrier := lowerPolar (fun s v => eval ι v s = 1) Y
  mul_mem' ha hb v hv := by simp [ha hv, hb hv]
  one_mem' _ _ := map_one _
  inv_mem' ha v hv := by simp [ha hv]

variable {ι} {S T : Set (GX G X)} {Y Z : Set (X → H)} {v : X → H} {w : GX G X}

@[simp]
theorem mem_V : v ∈ V ι S ↔ ∀ s ∈ S, eval ι v s = 1 := Iff.rfl

@[simp]
theorem mem_I : w ∈ I ι Y ↔ ∀ v ∈ Y, eval ι v w = 1 := Iff.rfl

instance (Y : Set (X → H)) : (I ι Y).Normal where
  conj_mem w hw g v hv := by simp [(mem_I.1 hw) v hv]

/-- The ideal of `Y` is the intersection of the kernels of evaluation at the points of `Y`. -/
theorem I_eq_iInf_ker (Y : Set (X → H)) : I ι Y = ⨅ v ∈ Y, (eval ι v).ker := by
  ext w
  simp

/-- A system vanishes on a set of points if and only if the points solve the system. -/
theorem subset_I_iff : S ⊆ I ι Y ↔ Y ⊆ V ι S :=
  subset_upperPolar_iff_subset_lowerPolar.symm

variable (ι) in
/-- Algebraic sets and ideals form an antitone Galois connection between systems of equations in
`G[X]` and sets of points in `H^X`. -/
theorem galoisConnection_V_I :
    GaloisConnection (fun S : Set (GX G X) => OrderDual.toDual (V ι S))
      (fun Y => (I ι (OrderDual.ofDual Y) : Set (GX G X))) :=
  gc_upperPolar_lowerPolar _

variable (ι) in
theorem V_antitone : Antitone (V ι : Set (GX G X) → Set (X → H)) :=
  upperPolar_anti _

variable (ι) in
theorem I_antitone : Antitone (I ι : Set (X → H) → Subgroup (GX G X)) :=
  fun _ _ h => lowerPolar_anti _ h

theorem subset_V_I (Y : Set (X → H)) : Y ⊆ V ι (I ι Y) :=
  subset_upperPolar_lowerPolar _ Y

/-- The algebraic set of the equations vanishing on an algebraic set is that algebraic set. -/
@[simp]
theorem V_I_V (S : Set (GX G X)) : V ι (I ι (V ι S)) = V ι S :=
  upperPolar_lowerPolar_upperPolar _ S

@[simp]
theorem I_V_I (Y : Set (X → H)) : I ι (V ι (I ι Y)) = I ι Y :=
  SetLike.coe_injective (lowerPolar_upperPolar_lowerPolar _ Y)

@[simp]
theorem V_empty : V ι (∅ : Set (GX G X)) = Set.univ :=
  upperPolar_empty _

@[simp]
theorem I_empty : I ι (∅ : Set (X → H)) = ⊤ :=
  SetLike.coe_injective ((lowerPolar_empty _).trans coe_top.symm)

@[simp]
theorem V_union (S T : Set (GX G X)) : V ι (S ∪ T) = V ι S ∩ V ι T :=
  upperPolar_union _ S T

@[simp]
theorem V_iUnion {κ : Sort*} (S : κ → Set (GX G X)) : V ι (⋃ k, S k) = ⋂ k, V ι (S k) :=
  upperPolar_iUnion _ S

/-- Pulling an algebraic set back along a tuple of words substitutes those words into its
equations. -/
theorem preimage_wordMap_V {Y : Type*} (w : Y → GX G X) (S : Set (GX G Y)) :
    wordMap ι w ⁻¹' V ι S =
      V ι ((eval (inl : G →* GX G X) w) '' S) := by
  ext v
  simp only [Set.mem_preimage, mem_V, Set.mem_image]
  constructor
  · intro hv s hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [← MonoidHom.comp_apply, eval_comp_eval]
    exact hv t ht
  · intro hv t ht
    have := hv _ ⟨t, ht, rfl⟩
    rwa [← MonoidHom.comp_apply, eval_comp_eval] at this

/-- The singleton of a tuple of coefficients is the solution set of the equations specifying
all its coordinates. -/
theorem singleton_comp_eq_V (g : X → G) :
    ({(ι ∘ g : X → H)} : Set (X → H)) =
      V ι (Set.range fun x => inr (FreeGroup.of x) * (inl (g x))⁻¹) := by
  ext v
  simp only [Set.mem_singleton_iff, mem_V, Set.mem_range]
  constructor
  · rintro rfl s ⟨x, rfl⟩
    simp
  · intro hv
    funext x
    have hx := hv _ ⟨x, rfl⟩
    simpa only [Function.comp_apply, map_mul, map_inv, eval_inl, eval_inr_of,
      mul_inv_eq_one] using hx

/-- If some coefficient remains nontrivial in `H`, an equation with that constant has no
solutions. -/
theorem V_singleton_inl_eq_empty {g : G} (hg : ι g ≠ 1) :
    V ι ({inl g} : Set (GX G X)) = ∅ := by
  ext v
  simp [hg]

@[simp]
theorem I_union (Y Z : Set (X → H)) : I ι (Y ∪ Z) = I ι Y ⊓ I ι Z :=
  SetLike.coe_injective ((lowerPolar_union _ Y Z).trans (coe_inf (I ι Y) (I ι Z)).symm)

@[simp]
theorem I_iUnion {κ : Sort*} (Y : κ → Set (X → H)) : I ι (⋃ k, Y k) = ⨅ k, I ι (Y k) :=
  SetLike.coe_injective ((lowerPolar_iUnion _ Y).trans (coe_iInf (S := fun k => I ι (Y k))).symm)

/-- A system and its normal closure have the same solutions. -/
@[simp]
theorem V_normalClosure (S : Set (GX G X)) : V ι (normalClosure S : Set (GX G X)) = V ι S := by
  refine (V_antitone ι subset_normalClosure).antisymm fun v hv => ?_
  have : normalClosure S ≤ (eval ι v).ker := normalClosure_le_normal fun s hs => mem_V.1 hv s hs
  exact mem_V.2 fun s hs => this hs

/-! ### Finite subsystems -/

/-- A homomorphism `m : G[X] →* G'[Y]` together with a map of points `θ` compatible with
evaluation carries finite subsystems of `m(S)` with the same solutions back to finite subsystems
of `S` with the same solutions. -/
theorem exists_finite_V_eq_of_map {G' Y : Type*} [Group G'] {ι : G →* H} {ι' : G' →* H}
    (m : GX G X →* GX G' Y) (θ : (X → H) → (Y → H))
    (hθ : ∀ v s, eval ι' (θ v) (m s) = eval ι v s) {S : Set (GX G X)}
    (h : ∃ T ⊆ m '' S, T.Finite ∧ V ι' T = V ι' (m '' S)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  obtain ⟨S₀, hS₀, hfin, hV⟩ := Set.exists_subset_image_finite_and.1 h
  have key (T : Set (GX G X)) : V ι T = θ ⁻¹' V ι' (m '' T) := by
    ext v
    simp [hθ]
  exact ⟨S₀, hS₀, hfin, by rw [key, key, hV]⟩

/-- If there are only finitely many points `X → H`, every system is equivalent to a finite
subsystem: one equation failing at each non-solution suffices. -/
theorem exists_finite_V_eq_of_finite {ι : G →* H} [Finite (X → H)] (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Finite ∧ V ι S₀ = V ι S := by
  have hw (v : ↥(V ι S)ᶜ) : ∃ s ∈ S, eval ι v s ≠ 1 := by
    have hv := v.2
    simpa only [Set.mem_compl_iff, mem_V, not_forall, exists_prop] using hv
  choose w hwS hw using hw
  have hsub : Set.range w ⊆ S := Set.range_subset_iff.2 hwS
  refine ⟨Set.range w, hsub, Set.finite_range w, (V_antitone ι hsub).antisymm' fun v hv => ?_⟩
  by_contra hvS
  exact hw ⟨v, hvS⟩ (mem_V.1 hv _ ⟨⟨v, hvS⟩, rfl⟩)

/-- If there is at most one point `X → H`, for instance when there are no variables, a single
equation suffices: a system with a solution is equivalent to the empty subsystem, and a system
without one is equivalent to any of its equations that fails at the point. -/
theorem exists_subsingleton_V_eq {ι : G →* H} [Subsingleton (X → H)] (S : Set (GX G X)) :
    ∃ S₀ ⊆ S, S₀.Subsingleton ∧ V ι S₀ = V ι S := by
  by_cases hS : ∃ s ∈ S, ∃ v, eval ι v s ≠ 1
  · obtain ⟨s, hs, v, hv⟩ := hS
    have hs₀ : V ι {s} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun u hu => hv (Subsingleton.elim v u ▸ mem_V.1 hu s rfl)
    refine ⟨{s}, Set.singleton_subset_iff.2 hs, Set.subsingleton_singleton, ?_⟩
    rw [hs₀, eq_comm, ← Set.subset_empty_iff, ← hs₀]
    exact V_antitone ι (Set.singleton_subset_iff.2 hs)
  · refine ⟨∅, Set.empty_subset S, Set.subsingleton_empty, ?_⟩
    simp only [not_exists, not_and, not_not] at hS
    rw [V_empty]
    exact (Set.eq_univ_of_forall fun v => mem_V.2 fun s hs => hS s hs v).symm

/-! ### Radicals -/

variable (ι) in
/-- The radical `Rad_H(S) = I_H(V_H(S))` of a system `S ⊆ G[X]` over `H`: the equations satisfied
by every solution of `S` in `H`. -/
def Rad (S : Set (GX G X)) : Subgroup (GX G X) :=
  I ι (V ι S)

theorem Rad_def (S : Set (GX G X)) : Rad ι S = I ι (V ι S) := (rfl)

@[simp]
theorem mem_Rad : w ∈ Rad ι S ↔ ∀ v ∈ V ι S, eval ι v w = 1 := Iff.rfl

instance (S : Set (GX G X)) : (Rad ι S).Normal :=
  inferInstanceAs (I ι (V ι S)).Normal

theorem subset_Rad (S : Set (GX G X)) : S ⊆ Rad ι S :=
  subset_I_iff.2 subset_rfl

/-- The radical of `S` contains the normal closure of `S`. -/
theorem normalClosure_le_Rad (S : Set (GX G X)) : normalClosure S ≤ Rad ι S :=
  normalClosure_le_normal (subset_Rad S)

variable (ι) in
theorem Rad_monotone : Monotone (Rad ι : Set (GX G X) → Subgroup (GX G X)) :=
  fun _ _ h => I_antitone ι (V_antitone ι h)

@[simp]
theorem V_Rad (S : Set (GX G X)) : V ι (Rad ι S : Set (GX G X)) = V ι S :=
  V_I_V S

/-- Taking radicals is idempotent. -/
@[simp]
theorem Rad_Rad (S : Set (GX G X)) : Rad ι (Rad ι S : Set (GX G X)) = Rad ι S := by
  rw [Rad_def, V_Rad, Rad_def]

@[simp]
theorem Rad_normalClosure (S : Set (GX G X)) :
    Rad ι (normalClosure S : Set (GX G X)) = Rad ι S := by
  rw [Rad_def, V_normalClosure, Rad_def]

@[simp]
theorem Rad_empty : Rad ι (∅ : Set (GX G X)) = I ι Set.univ := by
  rw [Rad_def, V_empty]

/-- For injective coefficients, the ideal of a point `ι ∘ g` with coordinates in the image of `G`
is the normal closure of the equations `x (g x)⁻¹`, `x ∈ X`. -/
theorem I_singleton_comp (hι : Function.Injective ι) (g : X → G) :
    I ι {ι ∘ g} = normalClosure (Set.range fun x => inr (FreeGroup.of x) * (inl (g x))⁻¹) := by
  refine le_antisymm (fun w hw => ?_) (normalClosure_le_normal ?_)
  · -- Modulo the normal closure `N` of the equations `x (g x)⁻¹`, every element of `G[X]` is
    -- congruent to the coefficient given by evaluation at `g`.
    set N := normalClosure (Set.range fun x => inr (FreeGroup.of x) * (inl (g x))⁻¹)
    have hπ : QuotientGroup.mk' N =
        ((QuotientGroup.mk' N).comp inl).comp (eval (.id G) g) := by
      refine hom_ext (MonoidHom.ext fun _ => by simp) (FreeGroup.ext_hom _ _ fun x => ?_)
      have : inr (FreeGroup.of x) * (inl (g x))⁻¹ ∈ N := subset_normalClosure ⟨x, rfl⟩
      simpa [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] using this
    have hw : eval (.id G) g w = 1 := by
      apply hι
      rw [map_one, ← MonoidHom.comp_apply, MonoidHom.comp_eval, MonoidHom.comp_id]
      exact mem_I.1 hw _ rfl
    rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, hπ]
    simp [hw]
  · rintro _ ⟨x, rfl⟩ v rfl
    simp

/-! ### Quotients of `G[X]` -/

namespace GX

variable (N : Subgroup (GX G X)) [N.Normal]

/-- The coefficient homomorphism `G →* G[X] ⧸ N` of a quotient of `G[X]`. -/
def quotientCoeff : G →* GX G X ⧸ N :=
  (QuotientGroup.mk' N).comp inl

theorem quotientCoeff_def : quotientCoeff N = (QuotientGroup.mk' N).comp inl := (rfl)

@[simp]
theorem quotientCoeff_apply (g : G) : quotientCoeff N g = ((inl g : GX G X) : GX G X ⧸ N) := (rfl)

variable {N}

/-- A `G`-homomorphism `G[X] ⧸ N → H`, composed with the quotient map, restricts to `ι` on the
coefficients. -/
theorem comp_mk'_comp_inl (φ : GHom (quotientCoeff N) ι) :
    ((φ : GX G X ⧸ N →* H).comp (QuotientGroup.mk' N)).comp inl = ι := by
  rw [MonoidHom.comp_assoc, ← quotientCoeff_def, φ.comp_coeff]

/-- A `G`-homomorphism `G[X] ⧸ N → H`, composed with the quotient map, is evaluation at its values
on the variables. -/
theorem eval_eq_comp_mk' (φ : GHom (quotientCoeff N) ι) :
    eval ι (fun x => φ (inr (FreeGroup.of x) : GX G X)) =
      (φ : GX G X ⧸ N →* H).comp (QuotientGroup.mk' N) := by
  simpa using eval_eq_of_comp_inl (comp_mk'_comp_inl φ)

variable (v) in
/-- Evaluation at a point `v` at which every equation of `N` vanishes, as a `G`-homomorphism
`G[X] ⧸ N → H`. -/
def quotientEvalGHom (hv : v ∈ V ι (N : Set (GX G X))) : GHom (quotientCoeff N) ι where
  toMonoidHom := QuotientGroup.lift N (eval ι v) fun w hw => mem_V.1 hv w hw
  map_coeff' := eval_inl ι v

@[simp]
theorem quotientEvalGHom_mk (hv : v ∈ V ι (N : Set (GX G X))) (w : GX G X) :
    quotientEvalGHom v hv (w : GX G X ⧸ N) = eval ι v w := (rfl)

variable (ι N) in
/-- The universal property of a quotient `G[X] ⧸ N`: `G`-homomorphisms `G[X] ⧸ N → H` correspond
to the points of `H^X` at which every equation of `N` vanishes, by restriction to the variables and
by evaluation. -/
def quotientHomEquiv : GHom (quotientCoeff N) ι ≃ V ι (N : Set (GX G X)) where
  toFun φ := ⟨fun x => φ (inr (FreeGroup.of x) : GX G X), mem_V.2 fun w hw => by
    rw [eval_eq_comp_mk', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff w).2 hw, map_one]⟩
  invFun v := quotientEvalGHom v.1 v.2
  left_inv φ := by
    refine GHom.ext fun q => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    exact DFunLike.congr_fun (eval_eq_comp_mk' φ) w
  right_inv v := Subtype.ext (funext fun x => eval_inr_of ι v.1 x)

@[simp]
theorem quotientHomEquiv_apply_coe (φ : GHom (quotientCoeff N) ι) (x : X) :
    (quotientHomEquiv ι N φ : X → H) x = φ (inr (FreeGroup.of x) : GX G X) := (rfl)

@[simp]
theorem quotientHomEquiv_symm_apply (v : V ι (N : Set (GX G X))) :
    (quotientHomEquiv ι N).symm v = quotientEvalGHom v v.2 := (rfl)

/-- A `G`-homomorphism out of `G[X] ⧸ N` is determined by its values on the variables. -/
@[ext]
theorem quotientGHom_ext {φ ψ : GHom (quotientCoeff N) ι}
    (h : ∀ x, φ (inr (FreeGroup.of x) : GX G X) = ψ (inr (FreeGroup.of x) : GX G X)) : φ = ψ :=
  (quotientHomEquiv ι N).injective (Subtype.ext (funext h))

/-- If `ι` is injective and the equations of `N` have a common zero in `H`, the coefficients
embed in `G[X] ⧸ N`. -/
theorem quotientCoeff_injective (hι : Function.Injective ι)
    (hN : (V ι (N : Set (GX G X))).Nonempty) : Function.Injective (quotientCoeff N) := by
  obtain ⟨v, hv⟩ := hN
  refine Function.Injective.of_comp (f := quotientEvalGHom v hv) ?_
  convert hι using 1
  ext g
  simp

end GX

/-! ### Coordinate groups and the group of a system -/

variable (ι) in
/-- The coordinate group `G_{R(S)} = G[X] ⧸ Rad_H(S)` of a system `S` over `H`. -/
abbrev CoordGroup (S : Set (GX G X)) : Type _ :=
  GX G X ⧸ Rad ι S

namespace CoordGroup

variable (ι) in
/-- The coefficient homomorphism `G →* G_{R(S)}`. -/
def coeff (S : Set (GX G X)) : G →* CoordGroup ι S :=
  GX.quotientCoeff _

@[simp]
theorem coeff_apply (S : Set (GX G X)) (g : G) :
    coeff ι S g = ((inl g : GX G X) : CoordGroup ι S) := (rfl)

variable (v) in
/-- Evaluation at a solution `v` of `S` in `H`, as a `G`-homomorphism `G_{R(S)} → H`. -/
def evalGHom (hv : v ∈ V ι S) : GHom (coeff ι S) ι :=
  GX.quotientEvalGHom v ((V_Rad (ι := ι) S).ge hv)

@[simp]
theorem evalGHom_mk (hv : v ∈ V ι S) (w : GX G X) :
    evalGHom v hv (w : CoordGroup ι S) = eval ι v w := (rfl)

variable (ι S) in
/-- The universal property of the coordinate group: `G`-homomorphisms `G_{R(S)} → H` correspond
to the solutions of `S` in `H`, by restriction to the variables and by evaluation. -/
def homEquiv : GHom (coeff ι S) ι ≃ V ι S :=
  (GX.quotientHomEquiv ι _).trans (Set.equivOfEq (V_Rad S))

@[simp]
theorem homEquiv_apply_coe (φ : GHom (coeff ι S) ι) (x : X) :
    (homEquiv ι S φ : X → H) x = φ (inr (FreeGroup.of x) : GX G X) := (rfl)

@[simp]
theorem homEquiv_symm_apply (v : V ι S) : (homEquiv ι S).symm v = evalGHom v v.2 := (rfl)

/-- A `G`-homomorphism out of `G_{R(S)}` is determined by its values on the variables. -/
@[ext]
theorem gHom_ext {φ ψ : GHom (coeff ι S) ι}
    (h : ∀ x, φ (inr (FreeGroup.of x) : GX G X) = ψ (inr (FreeGroup.of x) : GX G X)) : φ = ψ :=
  GX.quotientGHom_ext h

/-- If `ι` is injective and the system `S` has a solution in `H`, the coefficients embed in the
coordinate group `G_{R(S)}`. -/
theorem coeff_injective (hι : Function.Injective ι) (hS : (V ι S).Nonempty) :
    Function.Injective (coeff ι S) :=
  GX.quotientCoeff_injective hι (hS.mono (V_Rad (ι := ι) S).ge)

variable (ι) in
/-- The coordinate group `G_{R(S)}` of a system with a solution in a `G`-group `H`, as a
`G`-group. -/
@[expose] def toGGroup (hι : Function.Injective ι) (hS : (V ι S).Nonempty) : GGroup G :=
  ⟨CoordGroup ι S, coeff ι S, coeff_injective hι hS⟩

@[simp]
theorem toGGroup_coeff (hι : Function.Injective ι) (hS : (V ι S).Nonempty) :
    (toGGroup ι hι hS).coeff = coeff ι S := (rfl)

end CoordGroup

variable (G) in
/-- The group `G_S = G[X] ⧸ ncl(S)` presented over `G` by the system `S` of equations. -/
abbrev SystemGroup (S : Set (GX G X)) : Type _ :=
  GX G X ⧸ normalClosure S

namespace SystemGroup

/-- The coefficient homomorphism `G →* G_S`. -/
def coeff (S : Set (GX G X)) : G →* SystemGroup G S :=
  GX.quotientCoeff _

@[simp]
theorem coeff_apply (S : Set (GX G X)) (g : G) :
    coeff S g = ((inl g : GX G X) : SystemGroup G S) := (rfl)

variable (ι) in
/-- The canonical surjection `G_S →* G_{R(S)}`, a `G`-homomorphism. -/
def toCoordGroup (S : Set (GX G X)) : GHom (coeff S) (CoordGroup.coeff ι S) where
  toMonoidHom := QuotientGroup.map _ _ (.id _) (by simpa using normalClosure_le_Rad S)
  map_coeff' _ := (rfl)

variable (v) in
/-- Evaluation at a solution `v` of `S` in `H`, as a `G`-homomorphism `G_S → H`. -/
def evalGHom (hv : v ∈ V ι S) : GHom (coeff S) ι :=
  GX.quotientEvalGHom v ((V_normalClosure (ι := ι) S).ge hv)

@[simp]
theorem evalGHom_mk (hv : v ∈ V ι S) (w : GX G X) :
    evalGHom v hv (w : SystemGroup G S) = eval ι v w := (rfl)

variable (ι S) in
/-- The universal property of `G_S`: `G`-homomorphisms `G_S → H` correspond to the solutions of
`S` in `H`, by restriction to the variables and by evaluation. -/
def homEquiv : GHom (coeff S) ι ≃ V ι S :=
  (GX.quotientHomEquiv ι _).trans (Set.equivOfEq (V_normalClosure S))

@[simp]
theorem homEquiv_apply_coe (φ : GHom (coeff S) ι) (x : X) :
    (homEquiv ι S φ : X → H) x = φ (inr (FreeGroup.of x) : GX G X) := (rfl)

@[simp]
theorem homEquiv_symm_apply (v : V ι S) : (homEquiv ι S).symm v = evalGHom v v.2 := (rfl)

/-- A `G`-homomorphism out of `G_S` is determined by its values on the variables. -/
@[ext]
theorem gHom_ext {φ ψ : GHom (coeff S) ι}
    (h : ∀ x, φ (inr (FreeGroup.of x) : GX G X) = ψ (inr (FreeGroup.of x) : GX G X)) : φ = ψ :=
  GX.quotientGHom_ext h

@[simp]
theorem toCoordGroup_mk (S : Set (GX G X)) (w : GX G X) :
    toCoordGroup ι S (w : SystemGroup G S) = (w : CoordGroup ι S) := (rfl)

theorem toCoordGroup_surjective (S : Set (GX G X)) :
    Function.Surjective (toCoordGroup ι S) := by
  intro q
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨w, toCoordGroup_mk S w⟩

/-- If `ι` is injective and the system `S` has a solution in `H`, the coefficients embed in
`G_S`. -/
theorem coeff_injective (hι : Function.Injective ι) (hS : (V ι S).Nonempty) :
    Function.Injective (coeff S) :=
  GX.quotientCoeff_injective hι (hS.mono (V_normalClosure (ι := ι) S).ge)

/-- Restricting a `G`-homomorphism `G_{R(S)} → H` along `G_S → G_{R(S)}` gives the same solution
of `S`. -/
@[simp]
theorem homEquiv_comp_toCoordGroup (φ : GHom (CoordGroup.coeff ι S) ι) :
    homEquiv ι S (φ.comp (toCoordGroup ι S)) = CoordGroup.homEquiv ι S φ :=
  Subtype.ext (funext fun _ => by simp)

end SystemGroup

/-- Evaluation at a solution `v` on `G_S` factors through `G_S → G_{R(S)}`. -/
@[simp]
theorem CoordGroup.evalGHom_comp_toCoordGroup (hv : v ∈ V ι S) :
    (evalGHom v hv).comp (SystemGroup.toCoordGroup ι S) = SystemGroup.evalGHom v hv := by
  ext
  simp

/-! ### The radical is not the normal closure -/

section Pow

open FreeGroup

/-- Over a torsion-free group `H` with injective coefficients, the radical of the one-variable
equation `x ^ n = 1` (`n ≠ 0`) is the normal closure of `x`. -/
theorem Rad_pow_eq_normalClosure [IsMulTorsionFree H] (hι : Function.Injective ι) {n : ℕ}
    (hn : n ≠ 0) :
    Rad ι {(inr (of ()) : GX G Unit) ^ n} = normalClosure {inr (of ())} := by
  have hV : V ι {(inr (of ()) : GX G Unit) ^ n} = {ι ∘ fun _ => 1} := by
    ext v
    simp [hn, funext_iff, Unique.forall_iff]
  rw [Rad_def, hV, I_singleton_comp hι]
  simp [Set.range_unique]

/-- The normal closure of the one-variable equation `x ^ n` does not contain `x` when `n ≠ 1`. -/
theorem inr_of_notMem_normalClosure_pow {n : ℕ} (hn : n ≠ 1) (x : X) :
    (inr (of x) : GX G X) ∉ normalClosure {inr (of x) ^ n} := by
  -- Send the coefficients to `1` and the variables to a generator of `ℤ / n`.
  let f : GX G X →* Multiplicative (ZMod n) := eval 1 fun _ => .ofAdd 1
  have hle : normalClosure {inr (of x) ^ n} ≤ f.ker := by
    refine normalClosure_le_normal ?_
    rintro _ rfl
    simp [f, ← ofAdd_nsmul]
  intro h
  have : (Multiplicative.ofAdd 1 : Multiplicative (ZMod n)) = 1 := by simpa [f] using hle h
  exact hn (ZMod.one_eq_zero_iff.1 this)

/-- For `n ≠ 1`, the normal closure of `x ^ n` differs from the normal closure of `x`. -/
theorem normalClosure_pow_ne_normalClosure {n : ℕ} (hn : n ≠ 1) (x : X) :
    normalClosure {(inr (of x) : GX G X) ^ n} ≠ normalClosure {inr (of x)} := fun h =>
  inr_of_notMem_normalClosure_pow hn x (by rw [h]; exact subset_normalClosure rfl)

/-- Over `G = F(a, b)` with one variable `x`, the radical of `x²` is the normal closure of `x`,
which is not the normal closure of `x²`. -/
theorem rad_sq :
    Rad (.id (FreeGroup (Fin 2))) {(inr (of ()) : GX (FreeGroup (Fin 2)) Unit) ^ 2} =
        normalClosure {inr (of ())} ∧
      normalClosure {(inr (of ()) : GX (FreeGroup (Fin 2)) Unit) ^ 2} ≠
        normalClosure {inr (of ())} :=
  ⟨Rad_pow_eq_normalClosure Function.injective_id two_ne_zero,
    normalClosure_pow_ne_normalClosure (by decide) ()⟩

/-- The radical depends on the group in which solutions are taken: over `G = F(a, b)`, the
variable `x` lies in the radical of `x²` over `G`, but not over `G × ℤ/2`, where `(1, 1)` is a
nontrivial solution of `x² = 1`. -/
theorem rad_sq_prod_zmod_two :
    (inr (of ()) : GX (FreeGroup (Fin 2)) Unit) ∈
        Rad (.id (FreeGroup (Fin 2))) {inr (of ()) ^ 2} ∧
      (inr (of ()) : GX (FreeGroup (Fin 2)) Unit) ∉
        Rad (.inl (FreeGroup (Fin 2)) (Multiplicative (ZMod 2))) {inr (of ()) ^ 2} := by
  refine ⟨rad_sq.1 ▸ subset_normalClosure rfl, fun h => ?_⟩
  have hv : (fun _ => (1, .ofAdd 1)) ∈
      V (.inl (FreeGroup (Fin 2)) (Multiplicative (ZMod 2))) {inr (of ()) ^ 2} := by
    simp only [mem_V, Set.mem_singleton_iff, forall_eq, map_pow, eval_inr, lift_apply_of,
      Prod.pow_mk, one_pow, Prod.mk_eq_one, true_and]
    decide
  have := mem_Rad.1 h _ hv
  simp [Prod.ext_iff] at this

end Pow

end TauCeti.GroupAlgGeom
