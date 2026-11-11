/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import Mathlib.Algebra.Group.Commutator
import TauCeti.GroupTheory.FreeGroup.Centralizer
import Mathlib.Algebra.Group.End

/-!
# Systems of equations with free variables

Let `S ⊆ G[X]` be a system of equations and `Y` a set of further variables, which do not occur in
`S`. Regarded as a system `S'` in the variables `X ⊕ Y` (`TauCeti.GroupAlgGeom.addFreeVars`), its
solutions in a group `H` receiving the coefficients are the solutions of `S` together with
arbitrary values of the variables of `Y` (`TauCeti.GroupAlgGeom.mem_V_addFreeVars`).

* The group presented by `S'` is the free product of the group presented by `S` with the free
  group on `Y` (`TauCeti.GroupAlgGeom.SystemGroup.exists_mulEquiv_addFreeVars`).
* For coordinate groups there is only a surjection `G_{R(S)} ∗ F(Y) → G_{R(S')}`
  (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom`,
  `TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_surjective`). Its kernel consists of the elements
  killed by every homomorphism `G_{R(S)} ∗ F(Y) → H` given by a solution of `S` and values of `Y`
  (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_eq_one_iff`), so it is injective exactly when
  these homomorphisms separate the elements of the free product
  (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_injective_iff`), that is, when `G_{R(S)} ∗ F(Y)`
  is separated by `H` (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_injective_iff_isSeparatedBy`).
* This fails for `S = {[x, a], [y, b], [x, y]}` over the free group `F(a, b)` and one free
  variable `z` (`TauCeti.GroupAlgGeom.CoordGroup.not_injective_freeVarsHom_commutator`): every
  solution has `x = 1` or `y = 1`, so the commutator `[x, z y z⁻¹]` vanishes at every solution,
  but it is not trivial in `F_{R(S)} ∗ ⟨z⟩`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2 (the derived transformation D4 and Lemma 16).
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999).
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup

variable {G H X Y : Type*} [Group G] [Group H] (ι : G →* H)

/-! ### Adding free variables to a system -/

/-- The inclusion `G[X] → G[X ⊕ Y]` of the equations in the variables `X` into the equations in
the variables `X` and `Y`. -/
def inclFreeVars (G X Y : Type*) [Group G] : GX G X →* GX G (X ⊕ Y) :=
  eval (inl : G →* GX G (X ⊕ Y)) fun x => inr (FreeGroup.of (Sum.inl x))

@[simp]
theorem inclFreeVars_inl (g : G) : inclFreeVars G X Y (inl g) = inl g := by
  simp [inclFreeVars]

@[simp]
theorem inclFreeVars_inr_of (x : X) :
    inclFreeVars G X Y (inr (FreeGroup.of x)) = inr (FreeGroup.of (Sum.inl x)) := by
  simp [inclFreeVars]

/-- The inclusion `G[X] → G[X ⊕ Y]` is the renaming of the variables along `Sum.inl`. -/
theorem inclFreeVars_eq_map (G X Y : Type*) [Group G] :
    inclFreeVars G X Y = Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inl) :=
  hom_ext (MonoidHom.ext fun _ => by simp) (FreeGroup.ext_hom _ _ fun _ => by simp)

variable {ι} in
/-- Evaluating an equation in the variables `X` at a point of `H^(X ⊕ Y)` only uses the
coordinates of `X`. -/
@[simp]
theorem eval_inclFreeVars (v : X ⊕ Y → H) (w : GX G X) :
    eval ι v (inclFreeVars G X Y w) = eval ι (v ∘ Sum.inl) w := by
  rw [inclFreeVars_eq_map, eval_map, MonoidHom.comp_id]

/-- A system of equations in the variables `X`, regarded as a system in the variables `X` and
`Y`. -/
def addFreeVars (Y : Type*) (S : Set (GX G X)) : Set (GX G (X ⊕ Y)) :=
  inclFreeVars G X Y '' S

variable {S : Set (GX G X)}

theorem addFreeVars_def (Y : Type*) (S : Set (GX G X)) :
    addFreeVars Y S = inclFreeVars G X Y '' S := (rfl)

variable {ι} in
/-- The solutions of a system with free variables `Y` are the solutions of the system with
arbitrary values of the variables of `Y`. -/
theorem mem_V_addFreeVars {v : X ⊕ Y → H} :
    v ∈ V ι (addFreeVars Y S) ↔ v ∘ Sum.inl ∈ V ι S := by
  simp [addFreeVars_def]

/-! ### The quotient of `G[X]` by a normal subgroup, with free variables -/

/-- The homomorphism `G[X ⊕ Y] → (G[X] ⧸ N) ∗ F(Y)` sending the variables of `X` to their classes
and the variables of `Y` to the free generators. -/
private def toQuotientFreeVars (Y : Type*) (N : Subgroup (GX G X)) [N.Normal] :
    GX G (X ⊕ Y) →* GX (GX G X ⧸ N) Y :=
  eval ((inl : GX G X ⧸ N →* GX (GX G X ⧸ N) Y).comp (GX.quotientCoeff N))
    (Sum.elim (fun x => inl ((inr (FreeGroup.of x) : GX G X) : GX G X ⧸ N))
      fun y => inr (FreeGroup.of y))

private theorem toQuotientFreeVars_inclFreeVars (N : Subgroup (GX G X)) [N.Normal]
    (w : GX G X) : toQuotientFreeVars Y N (inclFreeVars G X Y w) = inl (w : GX G X ⧸ N) := by
  have h : (toQuotientFreeVars Y N).comp (inclFreeVars G X Y) =
      (inl : GX G X ⧸ N →* GX (GX G X ⧸ N) Y).comp (QuotientGroup.mk' N) :=
    hom_ext (MonoidHom.ext fun _ => by simp [toQuotientFreeVars])
      (FreeGroup.ext_hom _ _ fun _ => by simp [toQuotientFreeVars])
  exact DFunLike.congr_fun h w

private theorem toQuotientFreeVars_inr_map (N : Subgroup (GX G X)) [N.Normal] (w : FreeGroup Y) :
    toQuotientFreeVars Y N (inr (FreeGroup.map Sum.inr w)) = inr w := by
  have h : ((toQuotientFreeVars Y N).comp inr).comp (FreeGroup.map Sum.inr) = inr :=
    FreeGroup.ext_hom _ _ fun _ => by simp [toQuotientFreeVars]
  exact DFunLike.congr_fun h w

private theorem toQuotientFreeVars_surjective (N : Subgroup (GX G X)) [N.Normal] :
    Function.Surjective (toQuotientFreeVars Y N) := by
  intro w
  induction w using induction_on with
  | inl q =>
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨_, toQuotientFreeVars_inclFreeVars N t⟩
  | inr w => exact ⟨_, toQuotientFreeVars_inr_map N w⟩
  | mul x y hx hy =>
    obtain ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ := hx, hy
    exact ⟨s * t, map_mul _ s t⟩

/-- A homomorphism `(G[X] ⧸ N) ∗ F(Y) → H` given by a homomorphism on `G[X] ⧸ N` compatible with
the coefficients and by values of `Y`, restricted to `G[X ⊕ Y]`, is evaluation at the
corresponding point. -/
private theorem eval_toQuotientFreeVars {N : Subgroup (GX G X)} [N.Normal]
    (φ : GX G X ⧸ N →* H) (hφ : ∀ g, φ ((inl g : GX G X) : GX G X ⧸ N) = ι g) (u : Y → H)
    (t : GX G (X ⊕ Y)) :
    eval φ u (toQuotientFreeVars Y N t) =
      eval ι (Sum.elim (fun x => φ ((inr (FreeGroup.of x) : GX G X) : GX G X ⧸ N)) u) t := by
  have h : (eval φ u).comp (toQuotientFreeVars Y N) =
      eval ι (Sum.elim (fun x => φ ((inr (FreeGroup.of x) : GX G X) : GX G X ⧸ N)) u) :=
    hom_ext (MonoidHom.ext fun g => by simp [toQuotientFreeVars, hφ])
      (FreeGroup.ext_hom _ _ fun x => by cases x <;> simp [toQuotientFreeVars])
  exact DFunLike.congr_fun h t

/-! ### The group presented by a system with free variables -/

namespace SystemGroup

/-- The group presented by a system with free variables `Y` is the free product of the group
presented by the system with the free group on `Y`, compatibly with the variables. -/
theorem exists_mulEquiv_addFreeVars (Y : Type*) (S : Set (GX G X)) :
    ∃ e : SystemGroup G (addFreeVars Y S) ≃* GX (SystemGroup G S) Y,
      (∀ w : GX G X, e ((inclFreeVars G X Y w : GX G (X ⊕ Y)) : SystemGroup G (addFreeVars Y S)) =
        inl (w : SystemGroup G S)) ∧
      ∀ y : Y, e ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) :
        SystemGroup G (addFreeVars Y S)) = inr (FreeGroup.of y) := by
  have hle : normalClosure (addFreeVars Y S) ≤ (toQuotientFreeVars Y (normalClosure S)).ker :=
    normalClosure_le_normal <| by
      rintro _ ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, toQuotientFreeVars_inclFreeVars,
        (QuotientGroup.eq_one_iff s).2 (subset_normalClosure hs), map_one]
  have hle' : normalClosure S ≤ (normalClosure (addFreeVars Y S)).comap (inclFreeVars G X Y) :=
    normalClosure_le_normal fun s hs => subset_normalClosure (Set.mem_image_of_mem _ hs)
  let f : SystemGroup G (addFreeVars Y S) →* GX (SystemGroup G S) Y :=
    QuotientGroup.lift _ (toQuotientFreeVars Y (normalClosure S)) hle
  let g : GX (SystemGroup G S) Y →* SystemGroup G (addFreeVars Y S) :=
    lift (QuotientGroup.map _ _ (inclFreeVars G X Y) hle')
      (FreeGroup.lift fun y => ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) :
        SystemGroup G (addFreeVars Y S)))
  have hgf : g.comp f = .id _ :=
    QuotientGroup.monoidHom_ext _ <| hom_ext
      (MonoidHom.ext fun a => by simp [f, g, toQuotientFreeVars])
      (FreeGroup.ext_hom _ _ fun x => by cases x <;> simp [f, g, toQuotientFreeVars])
  have hfg : f.comp g = .id _ :=
    hom_ext
      (QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun w => by
        simp [f, g, toQuotientFreeVars_inclFreeVars])
      (FreeGroup.ext_hom _ _ fun y => by simp [f, g, toQuotientFreeVars])
  exact ⟨f.toMulEquiv g hgf hfg, fun w => toQuotientFreeVars_inclFreeVars _ w,
    fun y => by simp [f, toQuotientFreeVars]⟩

end SystemGroup

/-! ### The coordinate group of a system with free variables -/

namespace CoordGroup

/-- The inclusion of the variables induces a homomorphism from the coordinate group of a system
to the coordinate group of the system with free variables. -/
def inclFreeVarsHom (Y : Type*) (S : Set (GX G X)) :
    GHom (coeff ι S) (coeff ι (addFreeVars Y S)) :=
  homOfMapsToWordMap ι (addFreeVars Y S) S (fun x => inr (FreeGroup.of (Sum.inl x)))
    <| (mapsToWordMap_iff ..).2 fun v hv => by
      have h : wordMap ι (fun x : X => (inr (FreeGroup.of (Sum.inl x)) : GX G (X ⊕ Y))) v =
          v ∘ Sum.inl := funext fun _ => by simp
      exact h ▸ mem_V_addFreeVars.1 hv

variable {ι} in
@[simp]
theorem inclFreeVarsHom_mk (w : GX G X) :
    inclFreeVarsHom ι Y S (w : CoordGroup ι S) =
      ((inclFreeVars G X Y w : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) :=
  homOfMapsToWordMap_mk ..

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` from the free product of the coordinate group
of a system `S` with the free group on `Y` to the coordinate group of `S` with free variables
`Y`. -/
def freeVarsHom (Y : Type*) (S : Set (GX G X)) :
    GX (CoordGroup ι S) Y →* CoordGroup ι (addFreeVars Y S) :=
  eval (inclFreeVarsHom ι Y S).toMonoidHom fun y =>
    ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S))

variable {ι} in
@[simp]
theorem freeVarsHom_inl (q : CoordGroup ι S) :
    freeVarsHom ι Y S (inl q) = inclFreeVarsHom ι Y S q := by
  simp [freeVarsHom]

variable {ι} in
@[simp]
theorem freeVarsHom_inr_of (y : Y) :
    freeVarsHom ι Y S (inr (FreeGroup.of y)) =
      ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) := by
  simp [freeVarsHom]

variable {ι} in
private theorem freeVarsHom_toQuotientFreeVars (t : GX G (X ⊕ Y)) :
    freeVarsHom ι Y S (toQuotientFreeVars Y (Rad ι S) t) =
      (t : CoordGroup ι (addFreeVars Y S)) := by
  have h : (freeVarsHom ι Y S).comp (toQuotientFreeVars Y (Rad ι S)) =
      QuotientGroup.mk' (Rad ι (addFreeVars Y S)) :=
    hom_ext (MonoidHom.ext fun _ => by simp [toQuotientFreeVars])
      (FreeGroup.ext_hom _ _ fun x => by cases x <;> simp [toQuotientFreeVars])
  exact DFunLike.congr_fun h t

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is surjective. -/
theorem freeVarsHom_surjective (Y : Type*) (S : Set (GX G X)) :
    Function.Surjective (freeVarsHom ι Y S) := fun q => by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨_, freeVarsHom_toQuotientFreeVars t⟩

variable {ι} in
/-- The kernel of `G_{R(S)} ∗ F(Y) → G_{R(S')}` consists of the elements killed by every
homomorphism `G_{R(S)} ∗ F(Y) → H` given by a solution of `S` in `H` and values of `Y` in `H`. -/
theorem freeVarsHom_eq_one_iff {w : GX (CoordGroup ι S) Y} :
    freeVarsHom ι Y S w = 1 ↔
      ∀ (v : X → H) (hv : v ∈ V ι S) (u : Y → H), eval (evalGHom v hv).toMonoidHom u w = 1 := by
  obtain ⟨t, rfl⟩ := toQuotientFreeVars_surjective (Rad ι S) w
  have key (v : X → H) (hv : v ∈ V ι S) (u : Y → H) :
      eval (evalGHom v hv).toMonoidHom u (toQuotientFreeVars Y (Rad ι S) t) =
        eval ι (Sum.elim v u) t := by
    rw [eval_toQuotientFreeVars ι _ (by simp)]
    simp
  simp only [freeVarsHom_toQuotientFreeVars, QuotientGroup.eq_one_iff, mem_Rad, key]
  refine ⟨fun h v hv u => h _ (mem_V_addFreeVars.2 (by simpa using hv)), fun h v hv => ?_⟩
  simpa using h _ (mem_V_addFreeVars.1 hv) (v ∘ Sum.inr)

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is injective exactly when the homomorphisms
`G_{R(S)} ∗ F(Y) → H` given by a solution of `S` in `H` and values of `Y` in `H` separate the
nontrivial elements from `1`. -/
theorem freeVarsHom_injective_iff (Y : Type*) (S : Set (GX G X)) :
    Function.Injective (freeVarsHom ι Y S) ↔
      ∀ w : GX (CoordGroup ι S) Y, w ≠ 1 → ∃ (v : X → H) (hv : v ∈ V ι S) (u : Y → H),
        eval (evalGHom v hv).toMonoidHom u w ≠ 1 := by
  simp only [injective_iff_map_eq_one, freeVarsHom_eq_one_iff, ne_eq, ← not_forall]
  exact forall_congr' fun _ => not_imp_not.symm

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is injective exactly when the free product
`G_{R(S)} ∗ F(Y)` is separated by `H` over `G`. -/
theorem freeVarsHom_injective_iff_isSeparatedBy (Y : Type*) (S : Set (GX G X)) :
    Function.Injective (freeVarsHom ι Y S) ↔
      IsSeparatedBy ((inl : CoordGroup ι S →* GX (CoordGroup ι S) Y).comp (coeff ι S)) ι := by
  rw [freeVarsHom_injective_iff, isSeparatedBy_def]
  refine forall₂_congr fun w _ => ⟨fun ⟨v, hv, u, h⟩ => ?_, fun ⟨φ, h⟩ => ?_⟩
  · exact ⟨⟨eval (evalGHom v hv).toMonoidHom u, fun g => by simp⟩, h⟩
  · -- `φ` is given by its restriction `ψ` to the coordinate group and its values on `Y`.
    let ψ : GHom (coeff ι S) ι := ⟨(φ : GX (CoordGroup ι S) Y →* H).comp inl, φ.map_coeff⟩
    have hψ : evalGHom (homEquiv ι S ψ) (homEquiv ι S ψ).2 = ψ :=
      (homEquiv_symm_apply _).symm.trans ((homEquiv ι S).symm_apply_apply ψ)
    have hφ : eval ψ.toMonoidHom (fun y => φ (inr (FreeGroup.of y))) w = φ w :=
      (DFunLike.congr_fun (eq_eval (φ : GX (CoordGroup ι S) Y →* H)) w).symm
    refine ⟨_, (homEquiv ι S ψ).2, fun y => φ (inr (FreeGroup.of y)), ?_⟩
    rwa [hψ, hφ]

end CoordGroup

/-! ### A system whose free variables are not free in the coordinate group -/

section Commutator

open FreeGroup
open scoped commutatorElement

/-- The system `[x, a] = [y, b] = [x, y] = 1` over the free group `F(a, b)`. -/
private abbrev commutatorSystem : Set (GX (FreeGroup (Fin 2)) (Fin 2)) :=
  let x : GX (FreeGroup (Fin 2)) (Fin 2) := inr (of 0)
  let y : GX (FreeGroup (Fin 2)) (Fin 2) := inr (of 1)
  {⁅x, inl (of 0)⁆, ⁅y, inl (of 1)⁆, ⁅x, y⁆}

private theorem mem_V_commutatorSystem {v : Fin 2 → FreeGroup (Fin 2)} :
    v ∈ V (.id _) commutatorSystem ↔
      Commute (v 0) (of 0) ∧ Commute (v 1) (of 1) ∧ Commute (v 0) (v 1) := by
  simp [commutatorSystem, commutatorElement_eq_one_iff_commute]

/-- Every solution of `[x, a] = [y, b] = [x, y] = 1` in `F(a, b)` has `x = 1` or `y = 1`. -/
private theorem eq_one_or_eq_one_of_mem_V_commutatorSystem {v : Fin 2 → FreeGroup (Fin 2)}
    (hv : v ∈ V (.id _) commutatorSystem) : v 0 = 1 ∨ v 1 = 1 := by
  obtain ⟨h₀, h₁, h⟩ := mem_V_commutatorSystem.1 hv
  by_contra! hne
  have hab : Commute (of (0 : Fin 2)) (of 1) :=
    IsFreeGroup.commute_of_commute hne.2 (IsFreeGroup.commute_of_commute hne.1 h₀.symm h) h₁
  exact absurd hab.eq (by decide)

/-- The commutator `[x, z y z⁻¹]` in `F_{R(S)} ∗ ⟨z⟩`, for `S` the system
`[x, a] = [y, b] = [x, y] = 1`. -/
private abbrev commutatorWord :
    GX (CoordGroup (.id (FreeGroup (Fin 2))) commutatorSystem) Unit :=
  let x : GX (CoordGroup (.id (FreeGroup (Fin 2))) commutatorSystem) Unit :=
    inl ((inr (of 0) : GX (FreeGroup (Fin 2)) (Fin 2)) : CoordGroup (.id _) commutatorSystem)
  let y : GX (CoordGroup (.id (FreeGroup (Fin 2))) commutatorSystem) Unit :=
    inl ((inr (of 1) : GX (FreeGroup (Fin 2)) (Fin 2)) : CoordGroup (.id _) commutatorSystem)
  let z : GX (CoordGroup (.id (FreeGroup (Fin 2))) commutatorSystem) Unit := inr (of ())
  ⁅x, z * y * z⁻¹⁆

/-- The commutator `[x, z y z⁻¹]` is not trivial in `F_{R(S)} ∗ ⟨z⟩`: the solutions `(a, 1)` and
`(1, b)` give a homomorphism to the permutations of four points under which `x` and `y` go to
disjoint transpositions, and `z` can be sent to a transposition meeting both. -/
private theorem commutatorWord_ne_one : commutatorWord ≠ 1 := by
  have h₁ : ![of 0, 1] ∈ V (.id (FreeGroup (Fin 2))) commutatorSystem :=
    mem_V_commutatorSystem.2 (by simp)
  have h₂ : ![1, of 1] ∈ V (.id (FreeGroup (Fin 2))) commutatorSystem :=
    mem_V_commutatorSystem.2 (by simp)
  let ρ : FreeGroup (Fin 2) →* Equiv.Perm (Fin 2) := FreeGroup.lift fun _ => Equiv.swap 0 1
  let κ : CoordGroup (.id (FreeGroup (Fin 2))) commutatorSystem →* Equiv.Perm (Fin 2 ⊕ Fin 2) :=
    (Equiv.Perm.sumCongrHom (Fin 2) (Fin 2)).comp
      ((ρ.comp (CoordGroup.evalGHom _ h₁).toMonoidHom).prod
        (ρ.comp (CoordGroup.evalGHom _ h₂).toMonoidHom))
  let t : Equiv.Perm (Fin 2 ⊕ Fin 2) := Equiv.swap (Sum.inl 0) (Sum.inr 0)
  have hne : ⁅(Equiv.swap (Sum.inl 0) (Sum.inl 1) : Equiv.Perm (Fin 2 ⊕ Fin 2)),
      t * Equiv.swap (Sum.inr 0) (Sum.inr 1) * t⁆ ≠ 1 := by decide
  refine fun h => hne ?_
  simpa [commutatorWord, κ, ρ, t] using congrArg (eval κ fun _ => t) h

/-- For the system `S = {[x, a], [y, b], [x, y]}` over the free group `F(a, b)` and one free
variable `z`, the surjection `F_{R(S)} ∗ ⟨z⟩ → F_{R(S')}` is not injective. -/
theorem CoordGroup.not_injective_freeVarsHom_commutator :
    let x : GX (FreeGroup (Fin 2)) (Fin 2) := inr (of 0)
    let y : GX (FreeGroup (Fin 2)) (Fin 2) := inr (of 1)
    ¬Function.Injective (CoordGroup.freeVarsHom (.id (FreeGroup (Fin 2))) Unit
      {⁅x, inl (of 0)⁆, ⁅y, inl (of 1)⁆, ⁅x, y⁆}) := by
  intro _ _ h
  refine commutatorWord_ne_one ((injective_iff_map_eq_one _).1 h _ ?_)
  refine CoordGroup.freeVarsHom_eq_one_iff.2 fun v hv u => ?_
  obtain h | h := eq_one_or_eq_one_of_mem_V_commutatorSystem hv <;>
    simp [commutatorWord, h]

end Commutator

end TauCeti.GroupAlgGeom
