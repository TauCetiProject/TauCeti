/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Separated
public import Mathlib.Algebra.Group.Commutator
import TauCeti.GroupTheory.Coprod.NormalForm
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.GroupTheory.FreeGroup.CSA

/-!
# Systems of equations with free variables

Let `S ⊆ G[X]` be a system of equations and `Y` a set of further variables, which do not occur in
`S`. Regarded as a system `S'` in the variables `X ⊕ Y` (`TauCeti.GroupAlgGeom.addFreeVars`), its
solutions in a group `H` receiving the coefficients are the solutions of `S` together with
arbitrary values of the variables of `Y` (`TauCeti.GroupAlgGeom.V_addFreeVars`).

* The group presented by `S'` is the free product of the group presented by `S` with the free
  group on `Y` (`TauCeti.GroupAlgGeom.SystemGroup.addFreeVarsEquiv`).
* The coordinate group `G_{R(S)}` embeds in `G_{R(S')}`
  (`TauCeti.GroupAlgGeom.CoordGroup.inclFreeVarsHom_injective`), since an equation in the
  variables `X` lies in the radical of `S'` exactly when it lies in the radical of `S`
  (`TauCeti.GroupAlgGeom.inclFreeVars_mem_Rad_addFreeVars`).
* For coordinate groups there is only a surjective `G`-homomorphism
  `G_{R(S)} ∗ F(Y) → G_{R(S')}` (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom`,
  `TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_surjective`). Its kernel consists of the elements
  killed by every homomorphism `G_{R(S)} ∗ F(Y) → H` given by a solution of `S` and values of `Y`
  (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_eq_one_iff`), so it is injective exactly when
  these homomorphisms separate the elements of the free product
  (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_injective_iff`), that is, when `G_{R(S)} ∗ F(Y)`
  is separated by `H` (`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom_injective_iff_isSeparatedBy`).
* It is not injective when `Y` is nonempty and every solution of `S` kills one of two nontrivial
  elements `a`, `b` of `G_{R(S)}`
  (`TauCeti.GroupAlgGeom.CoordGroup.not_injective_freeVarsHom_of_forall_eq_one_or_eq_one`): the
  commutator `[a, z b z⁻¹]`, `z ∈ Y`, vanishes at every solution but is not trivial in
  `G_{R(S)} ∗ F(Y)`. This happens for `S = {[x, a], [y, b], [x, y]}` over the free group `F(a, b)`
  and one free variable `z`
  (`TauCeti.GroupAlgGeom.CoordGroup.not_injective_freeVarsHom_commutator`): every solution has
  `x = 1` or `y = 1`.
* More generally, a `G`-homomorphism `G_S ∗ F(Y) → G_T` of presented groups induces a
  `G`-homomorphism `G_{R(S)} ∗ F(Y) → G_{R(T)}` of coordinate groups
  (`TauCeti.GroupAlgGeom.CoordGroup.freeProdMap`), surjective if the first one is; `freeVarsHom` is
  the one induced by the isomorphism `G_S ∗ F(Y) ≃ G_{S'}`. This gives the coordinate groups along
  a Tietze isomorphism that adds free generators.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2 (the derived transformation D4 and Lemma 16).
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999).
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup

variable {G H X Y : Type*} [Group G] [Group H] {ι : G →* H}

/-! ### Adding free variables to a system -/

/-- The inclusion `G[X] → G[X ⊕ Y]` of the equations in the variables `X` into the equations in
the variables `X` and `Y`. -/
def inclFreeVars (G X Y : Type*) [Group G] : GX G X →* GX G (X ⊕ Y) :=
  eval (inl : G →* GX G (X ⊕ Y)) fun x => inr (FreeGroup.of (Sum.inl x))

/-- The inclusion `G[X] → G[X ⊕ Y]` is the renaming of the variables along `Sum.inl`. -/
theorem inclFreeVars_eq_map (G X Y : Type*) [Group G] :
    inclFreeVars G X Y = Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inl) :=
  hom_ext (MonoidHom.ext fun _ => by simp [inclFreeVars])
    (FreeGroup.ext_hom _ _ fun _ => by simp [inclFreeVars])

@[simp]
theorem inclFreeVars_inl (g : G) : inclFreeVars G X Y (inl g) = inl g := by
  simp [inclFreeVars_eq_map]

@[simp]
theorem inclFreeVars_inr (w : FreeGroup X) :
    inclFreeVars G X Y (inr w) = inr (FreeGroup.map Sum.inl w) := by
  simp [inclFreeVars_eq_map]

theorem inclFreeVars_inr_of (x : X) :
    inclFreeVars G X Y (inr (FreeGroup.of x)) = inr (FreeGroup.of (Sum.inl x)) := by
  simp

/-- Evaluating an equation in the variables `X` at a point of `H^(X ⊕ Y)` only uses the
coordinates of `X`. -/
@[simp]
theorem eval_inclFreeVars (v : X ⊕ Y → H) (w : GX G X) :
    eval ι v (inclFreeVars G X Y w) = eval ι (v ∘ Sum.inl) w := by
  rw [inclFreeVars_eq_map, eval_map, MonoidHom.comp_id]

/-- The inclusion `G[X] → G[X ⊕ Y]` is injective. -/
theorem inclFreeVars_injective : Function.Injective (inclFreeVars G X Y) :=
  Function.LeftInverse.injective (g := eval inl (Sum.elim (fun x => inr (FreeGroup.of x)) 1))
    fun _ => by simp

/-- The inclusion `G[Y] → G[X ⊕ Y]`, renaming the variables along `Sum.inr`, is injective. -/
theorem map_inr_injective :
    Function.Injective (Monoid.Coprod.map (.id G) (FreeGroup.map (Sum.inr : Y → X ⊕ Y))) :=
  Function.LeftInverse.injective (g := eval inl (Sum.elim 1 fun y => inr (FreeGroup.of y)))
    fun _ => by simp [eval_map]

/-- A system of equations in the variables `X`, regarded as a system in the variables `X` and
`Y`. -/
def addFreeVars (Y : Type*) (S : Set (GX G X)) : Set (GX G (X ⊕ Y)) :=
  inclFreeVars G X Y '' S

variable {S : Set (GX G X)}

theorem addFreeVars_def (Y : Type*) (S : Set (GX G X)) :
    addFreeVars Y S = inclFreeVars G X Y '' S := (rfl)

theorem mem_addFreeVars {t : GX G (X ⊕ Y)} :
    t ∈ addFreeVars Y S ↔ ∃ s ∈ S, inclFreeVars G X Y s = t := Iff.rfl

@[simp]
theorem inclFreeVars_mem_addFreeVars {w : GX G X} :
    inclFreeVars G X Y w ∈ addFreeVars Y S ↔ w ∈ S :=
  inclFreeVars_injective.mem_set_image

/-- The solutions of a system with free variables `Y` are the solutions of the system with
arbitrary values of the variables of `Y`. -/
@[simp]
theorem V_addFreeVars (Y : Type*) (S : Set (GX G X)) :
    V ι (addFreeVars Y S) = (· ∘ Sum.inl) ⁻¹' V ι S := by
  ext v
  simp [addFreeVars_def]

theorem mem_V_addFreeVars {v : X ⊕ Y → H} :
    v ∈ V ι (addFreeVars Y S) ↔ v ∘ Sum.inl ∈ V ι S := by
  simp

/-- An equation in the variables `X` lies in the radical of the system with free variables `Y`
exactly when it lies in the radical of the system. -/
theorem inclFreeVars_mem_Rad_addFreeVars {w : GX G X} :
    inclFreeVars G X Y w ∈ Rad ι (addFreeVars Y S) ↔ w ∈ Rad ι S := by
  simp only [mem_Rad, V_addFreeVars, Set.mem_preimage, eval_inclFreeVars]
  refine ⟨fun h v hv => ?_, fun h v hv => h _ hv⟩
  simpa using h (Sum.elim v 1) (by simpa using hv)

/-- The radical of the system with free variables `Y` pulls back along `G[X] → G[X ⊕ Y]` to the
radical of the system. -/
@[simp]
theorem comap_inclFreeVars_Rad (Y : Type*) (S : Set (GX G X)) :
    (Rad ι (addFreeVars Y S)).comap (inclFreeVars G X Y) = Rad ι S :=
  Subgroup.ext fun _ => inclFreeVars_mem_Rad_addFreeVars

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

/-! ### The group presented by a system with free variables -/

namespace SystemGroup

/-- The homomorphism `G_{S'} → G_S ∗ F(Y)` induced by `G[X ⊕ Y] → G_S ∗ F(Y)`. -/
private def toFreeProd (Y : Type*) (S : Set (GX G X)) :
    SystemGroup G (addFreeVars Y S) →* GX (SystemGroup G S) Y :=
  QuotientGroup.lift _ (toQuotientFreeVars Y (normalClosure S)) <| normalClosure_le_normal <| by
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, toQuotientFreeVars_inclFreeVars,
      (QuotientGroup.eq_one_iff s).2 (subset_normalClosure hs), map_one]

/-- The homomorphism `G_S ∗ F(Y) → G_{S'}` induced by the inclusion of the variables of `X` and
of `Y`. -/
private def ofFreeProd (Y : Type*) (S : Set (GX G X)) :
    GX (SystemGroup G S) Y →* SystemGroup G (addFreeVars Y S) :=
  lift (QuotientGroup.map _ _ (inclFreeVars G X Y)
      (normalClosure_le_normal fun _ hs => subset_normalClosure (Set.mem_image_of_mem _ hs)))
    (FreeGroup.lift fun y => ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) :
      SystemGroup G (addFreeVars Y S)))

/-- The group presented by a system with free variables `Y` is the free product of the group
presented by the system with the free group on `Y`: the class of a word in the variables of `X`
goes to its class in the first factor, and each variable of `Y` to the corresponding free
generator. -/
def addFreeVarsEquiv (Y : Type*) (S : Set (GX G X)) :
    SystemGroup G (addFreeVars Y S) ≃* GX (SystemGroup G S) Y :=
  (toFreeProd Y S).toMulEquiv (ofFreeProd Y S)
    (QuotientGroup.monoidHom_ext _ <| hom_ext
      (MonoidHom.ext fun _ => by simp [toFreeProd, ofFreeProd, toQuotientFreeVars])
      (FreeGroup.ext_hom _ _ fun x => by
        cases x <;> simp [toFreeProd, ofFreeProd, toQuotientFreeVars]))
    (hom_ext
      (QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun _ => by
        simp [toFreeProd, ofFreeProd, toQuotientFreeVars_inclFreeVars])
      (FreeGroup.ext_hom _ _ fun _ => by simp [toFreeProd, ofFreeProd, toQuotientFreeVars]))

@[simp]
theorem addFreeVarsEquiv_mk_inclFreeVars (w : GX G X) :
    addFreeVarsEquiv Y S (inclFreeVars G X Y w : SystemGroup G (addFreeVars Y S)) =
      inl (w : SystemGroup G S) :=
  toQuotientFreeVars_inclFreeVars _ w

@[simp]
theorem addFreeVarsEquiv_mk_inl (g : G) :
    addFreeVarsEquiv Y S ((inl g : GX G (X ⊕ Y)) : SystemGroup G (addFreeVars Y S)) =
      inl ((inl g : GX G X) : SystemGroup G S) := by
  simpa using addFreeVarsEquiv_mk_inclFreeVars (Y := Y) (S := S) (inl g)

@[simp]
theorem addFreeVarsEquiv_mk_inr_map_inl (w : FreeGroup X) :
    addFreeVarsEquiv Y S ((inr (FreeGroup.map Sum.inl w) : GX G (X ⊕ Y)) :
      SystemGroup G (addFreeVars Y S)) = inl ((inr w : GX G X) : SystemGroup G S) := by
  simpa using addFreeVarsEquiv_mk_inclFreeVars (Y := Y) (S := S) (inr w)

@[simp]
theorem addFreeVarsEquiv_mk_inr_map_inr (w : FreeGroup Y) :
    addFreeVarsEquiv Y S ((inr (FreeGroup.map Sum.inr w) : GX G (X ⊕ Y)) :
      SystemGroup G (addFreeVars Y S)) = inr w :=
  toQuotientFreeVars_inr_map _ w

@[simp]
theorem addFreeVarsEquiv_mk_inr_of_inl (x : X) :
    addFreeVarsEquiv Y S ((inr (FreeGroup.of (Sum.inl x)) : GX G (X ⊕ Y)) :
      SystemGroup G (addFreeVars Y S)) =
      inl ((inr (FreeGroup.of x) : GX G X) : SystemGroup G S) :=
  addFreeVarsEquiv_mk_inr_map_inl (FreeGroup.of x)

@[simp]
theorem addFreeVarsEquiv_mk_inr_of_inr (y : Y) :
    addFreeVarsEquiv Y S ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) :
      SystemGroup G (addFreeVars Y S)) = inr (FreeGroup.of y) :=
  addFreeVarsEquiv_mk_inr_map_inr (FreeGroup.of y)

@[simp]
theorem addFreeVarsEquiv_symm_inl_mk (w : GX G X) :
    (addFreeVarsEquiv Y S).symm (inl (w : SystemGroup G S)) =
      (inclFreeVars G X Y w : SystemGroup G (addFreeVars Y S)) :=
  (MulEquiv.symm_apply_eq _).2 (addFreeVarsEquiv_mk_inclFreeVars w).symm

@[simp]
theorem addFreeVarsEquiv_symm_inr (w : FreeGroup Y) :
    (addFreeVarsEquiv Y S).symm (inr w) =
      ((inr (FreeGroup.map Sum.inr w) : GX G (X ⊕ Y)) : SystemGroup G (addFreeVars Y S)) :=
  (MulEquiv.symm_apply_eq _).2 (addFreeVarsEquiv_mk_inr_map_inr w).symm

/-- Under `G_S ∗ F(Y) ≃ G_{S'}`, evaluation at a solution `v` of the system with free
variables `Y` is evaluation at the restriction of `v` to `X` on `G_S` and at the values of `v`
on `Y`. -/
@[simp]
theorem evalGHom_addFreeVarsEquiv_symm {v : X ⊕ Y → H} (hv : v ∈ V ι (addFreeVars Y S))
    (w : GX (SystemGroup G S) Y) :
    evalGHom v hv ((addFreeVarsEquiv Y S).symm w) =
      eval (evalGHom (v ∘ Sum.inl) (mem_V_addFreeVars.1 hv) : SystemGroup G S →* H)
        (v ∘ Sum.inr) w := by
  induction w using induction_on with
  | inl q => induction q using QuotientGroup.induction_on; simp
  | inr w => simp
  | mul x y hx hy => simp [hx, hy]

end SystemGroup

/-! ### Coordinate groups and homomorphisms of presented groups with free variables -/

namespace CoordGroup

variable {X' : Type*} {S : Set (GX G X)} {T : Set (GX G X')}
  (ψ : GHom ((inl : SystemGroup G S →* GX (SystemGroup G S) Y).comp (SystemGroup.coeff S))
    (SystemGroup.coeff T))

variable (ι) in
/-- The homomorphism `G_{R(S)} → G_{R(T)}` induced by `G_S → G_S ∗ F(Y) → G_T`: evaluation at the
solution of `S` in `G_{R(T)}` given by `G_S → G_S ∗ F(Y) → G_T → G_{R(T)}`, since `G_{R(T)}` is
separated by `H`. -/
private def inlCoordMap : GHom (coeff ι S) (coeff ι T) :=
  evalGHomOfIsSeparatedBy (isSeparatedBy_coeff T) _ (SystemGroup.homEquiv _ S
    ((SystemGroup.toCoordGroup ι T).comp (ψ.comp ⟨inl, fun _ => rfl⟩))).property

variable (ι) in
/-- A `G`-homomorphism `ψ : G_S ∗ F(Y) → G_T` of presented groups induces a `G`-homomorphism
`G_{R(S)} ∗ F(Y) → G_{R(T)}` of coordinate groups, compatible with the projections
`G_S → G_{R(S)}` and `G_T → G_{R(T)}`. -/
def freeProdMap :
    GHom ((inl : CoordGroup ι S →* GX (CoordGroup ι S) Y).comp (coeff ι S)) (coeff ι T) where
  toMonoidHom := lift (inlCoordMap ι ψ : CoordGroup ι S →* CoordGroup ι T)
    (((SystemGroup.toCoordGroup ι T : SystemGroup G T →* CoordGroup ι T).comp
      (ψ : GX (SystemGroup G S) Y →* SystemGroup G T)).comp inr)
  map_coeff' g := by simp

/-- On `G_{R(S)}`, the induced homomorphism is `G_S → G_S ∗ F(Y) → G_T → G_{R(T)}`. -/
@[simp]
theorem freeProdMap_inl (w : GX G X) :
    freeProdMap ι ψ (inl (w : CoordGroup ι S)) =
      SystemGroup.toCoordGroup ι T (ψ (inl (w : SystemGroup G S))) := by
  simp [freeProdMap, inlCoordMap, GHom.coe_comp]

/-- On `F(Y)`, the induced homomorphism is `F(Y) → G_S ∗ F(Y) → G_T → G_{R(T)}`. -/
@[simp]
theorem freeProdMap_inr (w : FreeGroup Y) :
    freeProdMap ι ψ (inr w) = SystemGroup.toCoordGroup ι T (ψ (inr w)) := by
  simp [freeProdMap]

/-- The homomorphism of coordinate groups induced by `ψ : G_S ∗ F(Y) → G_T` is `ψ` on the classes
of the elements of `G_S ∗ F(Y)`. -/
@[simp]
theorem freeProdMap_map_toCoordGroup (w : GX (SystemGroup G S) Y) :
    freeProdMap ι ψ
        (Monoid.Coprod.map (SystemGroup.toCoordGroup ι S : SystemGroup G S →* CoordGroup ι S)
          (.id _) w) =
      SystemGroup.toCoordGroup ι T (ψ w) :=
  DFunLike.congr_fun (Monoid.Coprod.hom_ext
    (f := (freeProdMap ι ψ : GX (CoordGroup ι S) Y →* CoordGroup ι T).comp
      (Monoid.Coprod.map (SystemGroup.toCoordGroup ι S : SystemGroup G S →* CoordGroup ι S)
        (.id _)))
    (g := (SystemGroup.toCoordGroup ι T : SystemGroup G T →* CoordGroup ι T).comp ψ)
    (QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun _ => by simp))
    (MonoidHom.ext fun _ => by simp)) w

variable {ψ} in
/-- A surjective homomorphism of presented groups induces a surjective homomorphism of
coordinate groups. -/
theorem freeProdMap_surjective (hψ : Function.Surjective ψ) :
    Function.Surjective (freeProdMap ι ψ) := fun c => by
  obtain ⟨q, rfl⟩ := SystemGroup.toCoordGroup_surjective (ι := ι) T c
  obtain ⟨w, rfl⟩ := hψ q
  exact ⟨_, freeProdMap_map_toCoordGroup ψ w⟩

end CoordGroup

/-! ### The coordinate group of a system with free variables -/

namespace CoordGroup

/-- The `G`-homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` from the free product of the coordinate
group of a system `S` with the free group on `Y` to the coordinate group of `S` with free
variables `Y`, induced by the isomorphism `G_S ∗ F(Y) ≃ G_{S'}` of presented groups. -/
def freeVarsHom (ι : G →* H) (Y : Type*) (S : Set (GX G X)) :
    GHom ((inl : CoordGroup ι S →* GX (CoordGroup ι S) Y).comp (coeff ι S))
      (coeff ι (addFreeVars Y S)) :=
  freeProdMap ι (GHom.ofMulEquiv (SystemGroup.addFreeVarsEquiv Y S).symm fun g => by simp)

/-- The inclusion of the variables induces a homomorphism from the coordinate group of a system
to the coordinate group of the system with free variables: the restriction of
`G_{R(S)} ∗ F(Y) → G_{R(S')}` to the first factor. -/
def inclFreeVarsHom (ι : G →* H) (Y : Type*) (S : Set (GX G X)) :
    GHom (coeff ι S) (coeff ι (addFreeVars Y S)) where
  toMonoidHom := (freeVarsHom ι Y S : GX (CoordGroup ι S) Y →* CoordGroup ι (addFreeVars Y S)).comp
    inl
  map_coeff' := (freeVarsHom ι Y S).map_coeff

@[simp]
theorem freeVarsHom_inl (q : CoordGroup ι S) :
    freeVarsHom ι Y S (inl q) = inclFreeVarsHom ι Y S q :=
  (rfl)

@[simp]
theorem inclFreeVarsHom_mk (w : GX G X) :
    inclFreeVarsHom ι Y S (w : CoordGroup ι S) =
      ((inclFreeVars G X Y w : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) := by
  simp [← freeVarsHom_inl, freeVarsHom]

/-- The coordinate group of a system embeds in the coordinate group of the system with free
variables. -/
theorem inclFreeVarsHom_injective (ι : G →* H) (Y : Type*) (S : Set (GX G X)) :
    Function.Injective (inclFreeVarsHom ι Y S) := by
  refine (injective_iff_map_eq_one _).2 fun q hq => ?_
  induction q using QuotientGroup.induction_on with | H w => ?_
  rw [inclFreeVarsHom_mk, QuotientGroup.eq_one_iff, inclFreeVars_mem_Rad_addFreeVars] at hq
  exact (QuotientGroup.eq_one_iff w).2 hq

/-- Evaluation at a solution `v` of the system with free variables `Y` restricts, on the
coordinate group of the system, to evaluation at the restriction of `v` to `X`. -/
@[simp]
theorem evalGHom_inclFreeVarsHom {v : X ⊕ Y → H} (hv : v ∈ V ι (addFreeVars Y S))
    (q : CoordGroup ι S) :
    evalGHom v hv (inclFreeVarsHom ι Y S q) =
      evalGHom (v ∘ Sum.inl) (mem_V_addFreeVars.1 hv) q := by
  induction q using QuotientGroup.induction_on
  simp

@[simp]
theorem evalGHom_comp_inclFreeVarsHom {v : X ⊕ Y → H} (hv : v ∈ V ι (addFreeVars Y S)) :
    (evalGHom v hv).comp (inclFreeVarsHom ι Y S) =
      evalGHom (v ∘ Sum.inl) (mem_V_addFreeVars.1 hv) :=
  GHom.ext fun _ => by simp

@[simp]
theorem freeVarsHom_inr (w : FreeGroup Y) :
    freeVarsHom ι Y S (inr w) =
      ((inr (FreeGroup.map Sum.inr w) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) := by
  simp [freeVarsHom]

theorem freeVarsHom_inr_of (y : Y) :
    freeVarsHom ι Y S (inr (FreeGroup.of y)) =
      ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) := by
  simp

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is surjective. -/
theorem freeVarsHom_surjective (ι : G →* H) (Y : Type*) (S : Set (GX G X)) :
    Function.Surjective (freeVarsHom ι Y S) :=
  freeProdMap_surjective (GHom.ofMulEquiv_bijective _ _).2

/-- Evaluation at a solution `v` of the system with free variables `Y` is, on
`G_{R(S)} ∗ F(Y)`, evaluation at the restriction of `v` to `X` on `G_{R(S)}` and at the values of
`v` on `Y`. -/
@[simp]
theorem evalGHom_freeVarsHom {v : X ⊕ Y → H} (hv : v ∈ V ι (addFreeVars Y S))
    (w : GX (CoordGroup ι S) Y) :
    evalGHom v hv (freeVarsHom ι Y S w) =
      eval (evalGHom (v ∘ Sum.inl) (mem_V_addFreeVars.1 hv) : CoordGroup ι S →* H)
        (v ∘ Sum.inr) w := by
  induction w using induction_on with
  | inl q => simp
  | inr w => simp
  | mul x y hx hy => simp [hx, hy]

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is compatible, through `G_S ∗ F(Y) ≃ G_{S'}`,
with the projections `G_S → G_{R(S)}` and `G_{S'} → G_{R(S')}`. -/
@[simp]
theorem freeVarsHom_map_toCoordGroup (w : GX (SystemGroup G S) Y) :
    freeVarsHom ι Y S
        (Monoid.Coprod.map (SystemGroup.toCoordGroup ι S : SystemGroup G S →* CoordGroup ι S)
          (.id _) w) =
      SystemGroup.toCoordGroup ι (addFreeVars Y S)
        ((SystemGroup.addFreeVarsEquiv Y S).symm w) := by
  simp [freeVarsHom]

/-- The embedding `G_{R(S)} → G_{R(S')}` is compatible, through `G_S → G_S ∗ F(Y) ≃ G_{S'}`, with
the projections `G_S → G_{R(S)}` and `G_{S'} → G_{R(S')}`. -/
@[simp]
theorem inclFreeVarsHom_toCoordGroup (q : SystemGroup G S) :
    inclFreeVarsHom ι Y S (SystemGroup.toCoordGroup ι S q) =
      SystemGroup.toCoordGroup ι (addFreeVars Y S)
        ((SystemGroup.addFreeVarsEquiv Y S).symm (inl q)) := by
  simpa using freeVarsHom_map_toCoordGroup (ι := ι) (inl q)

/-- The kernel of `G_{R(S)} ∗ F(Y) → G_{R(S')}` consists of the elements killed by every
homomorphism `G_{R(S)} ∗ F(Y) → H` given by a solution of `S` in `H` and values of `Y` in `H`. -/
theorem freeVarsHom_eq_one_iff {w : GX (CoordGroup ι S) Y} :
    freeVarsHom ι Y S w = 1 ↔
      ∀ (v : X → H) (hv : v ∈ V ι S) (u : Y → H),
        eval (evalGHom v hv : CoordGroup ι S →* H) u w = 1 := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (freeVarsHom ι Y S w)
  rw [← ht, QuotientGroup.eq_one_iff, mem_Rad]
  refine ⟨fun h v hv u => ?_, fun h v hv => ?_⟩
  · have hv' : Sum.elim v u ∈ V ι (addFreeVars Y S) := mem_V_addFreeVars.2 (by simpa using hv)
    simpa [← evalGHom_mk hv', ht] using h _ hv'
  · simpa [← evalGHom_mk hv, ht] using h _ (mem_V_addFreeVars.1 hv) (v ∘ Sum.inr)

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is injective exactly when the homomorphisms
`G_{R(S)} ∗ F(Y) → H` given by a solution of `S` in `H` and values of `Y` in `H` separate the
nontrivial elements from `1`. -/
theorem freeVarsHom_injective_iff (ι : G →* H) (Y : Type*) (S : Set (GX G X)) :
    Function.Injective (freeVarsHom ι Y S) ↔
      ∀ w : GX (CoordGroup ι S) Y, w ≠ 1 → ∃ (v : X → H) (hv : v ∈ V ι S) (u : Y → H),
        eval (evalGHom v hv : CoordGroup ι S →* H) u w ≠ 1 := by
  simp only [injective_iff_map_eq_one, freeVarsHom_eq_one_iff, ne_eq, ← not_forall]
  exact forall_congr' fun _ => not_imp_not.symm

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is injective exactly when the free product
`G_{R(S)} ∗ F(Y)` is separated by `H` over `G`. -/
theorem freeVarsHom_injective_iff_isSeparatedBy (ι : G →* H) (Y : Type*) (S : Set (GX G X)) :
    Function.Injective (freeVarsHom ι Y S) ↔
      IsSeparatedBy ((inl : CoordGroup ι S →* GX (CoordGroup ι S) Y).comp (coeff ι S)) ι := by
  rw [freeVarsHom_injective_iff, isSeparatedBy_def]
  refine forall₂_congr fun w _ => ⟨fun ⟨v, hv, u, h⟩ => ?_, fun ⟨φ, h⟩ => ?_⟩
  · exact ⟨⟨eval (evalGHom v hv).toMonoidHom u, fun g => by simp⟩, h⟩
  · -- `φ` is given by its restriction `ψ` to the coordinate group and its values on `Y`.
    let ψ : GHom (coeff ι S) ι := ⟨(φ : GX (CoordGroup ι S) Y →* H).comp inl, φ.map_coeff⟩
    have hψ : evalGHom (homEquiv ι S ψ) (homEquiv ι S ψ).property = ψ :=
      (homEquiv_symm_apply _).symm.trans ((homEquiv ι S).symm_apply_apply ψ)
    have hφ : eval (ψ : CoordGroup ι S →* H) (fun y => φ (inr (FreeGroup.of y))) w = φ w :=
      (DFunLike.congr_fun (eq_eval (φ : GX (CoordGroup ι S) Y →* H)) w).symm
    refine ⟨_, (homEquiv ι S ψ).property, fun y => φ (inr (FreeGroup.of y)), ?_⟩
    rwa [hψ, hφ]

/-- If every solution of `S` in `H` kills one of two nontrivial elements `a`, `b` of `G_{R(S)}`,
then for nonempty `Y` the surjection `G_{R(S)} ∗ F(Y) → G_{R(S')}` is not injective: it kills the
commutator `[a, z b z⁻¹]`, `z ∈ Y`, which is not trivial in the free product. -/
theorem not_injective_freeVarsHom_of_forall_eq_one_or_eq_one [Nonempty Y] {a b : CoordGroup ι S}
    (ha : a ≠ 1) (hb : b ≠ 1)
    (h : ∀ (v : X → H) (hv : v ∈ V ι S), evalGHom v hv a = 1 ∨ evalGHom v hv b = 1) :
    ¬Function.Injective (freeVarsHom ι Y S) := fun hinj => by
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine commutatorElement_inl_conj_ne_one ha hb (FreeGroup.of_ne_one y)
    ((injective_iff_map_eq_one _).1 hinj _ (freeVarsHom_eq_one_iff.2 fun v hv u => ?_))
  obtain h | h := h v hv <;> simp [h]

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
  exact IsFreeGroup.isCommTransitive.eq_one_or_eq_one_of_not_commute
    (fun hab => absurd hab.eq (by decide)) h₀.symm h h₁

/-- For the system `S = {[x, a], [y, b], [x, y]}` over the free group `F(a, b)` and one free
variable `z`, the surjection `F_{R(S)} ∗ ⟨z⟩ → F_{R(S')}` is not injective: every solution has
`x = 1` or `y = 1`, and the solutions `(a, 1)` and `(1, b)` show that `x` and `y` are not trivial
in `F_{R(S)}`. -/
theorem CoordGroup.not_injective_freeVarsHom_commutator :
    let x : GX (FreeGroup (Fin 2)) (Fin 2) := inr (of 0)
    let y : GX (FreeGroup (Fin 2)) (Fin 2) := inr (of 1)
    ¬Function.Injective (CoordGroup.freeVarsHom (.id (FreeGroup (Fin 2))) Unit
      {⁅x, inl (of 0)⁆, ⁅y, inl (of 1)⁆, ⁅x, y⁆}) := by
  intro _ _
  have h₁ : ![of 0, 1] ∈ V (.id (FreeGroup (Fin 2))) commutatorSystem :=
    mem_V_commutatorSystem.2 (by simp)
  have h₂ : ![1, of 1] ∈ V (.id (FreeGroup (Fin 2))) commutatorSystem :=
    mem_V_commutatorSystem.2 (by simp)
  exact CoordGroup.not_injective_freeVarsHom_of_forall_eq_one_or_eq_one
    (CoordGroup.genericPoint_ne_one_iff (x := 0).2 ⟨_, h₁, by simp⟩)
    (CoordGroup.genericPoint_ne_one_iff (x := 1).2 ⟨_, h₂, by simp⟩)
    fun _ hv => by simpa using eq_one_or_eq_one_of_mem_V_commutatorSystem hv

end Commutator

end TauCeti.GroupAlgGeom
