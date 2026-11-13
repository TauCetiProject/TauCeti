/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import Mathlib.Algebra.Group.Commutator
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Centralizer
import Mathlib.Algebra.Group.End

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

variable {ι} in
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

variable {ι} in
/-- The solutions of a system with free variables `Y` are the solutions of the system with
arbitrary values of the variables of `Y`. -/
@[simp]
theorem V_addFreeVars (Y : Type*) (S : Set (GX G X)) :
    V ι (addFreeVars Y S) = (· ∘ Sum.inl) ⁻¹' V ι S := by
  ext v
  simp [addFreeVars_def]

variable {ι} in
theorem mem_V_addFreeVars {v : X ⊕ Y → H} :
    v ∈ V ι (addFreeVars Y S) ↔ v ∘ Sum.inl ∈ V ι S := by
  simp

variable {ι} in
/-- An equation in the variables `X` lies in the radical of the system with free variables `Y`
exactly when it lies in the radical of the system. -/
theorem inclFreeVars_mem_Rad_addFreeVars {w : GX G X} :
    inclFreeVars G X Y w ∈ Rad ι (addFreeVars Y S) ↔ w ∈ Rad ι S := by
  simp only [mem_Rad, V_addFreeVars, Set.mem_preimage, eval_inclFreeVars]
  refine ⟨fun h v hv => ?_, fun h v hv => h _ hv⟩
  simpa using h (Sum.elim v 1) (by simpa using hv)

variable {ι} in
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

variable {ι} in
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

/-- The coordinate group of a system embeds in the coordinate group of the system with free
variables. -/
theorem inclFreeVarsHom_injective (Y : Type*) (S : Set (GX G X)) :
    Function.Injective (inclFreeVarsHom ι Y S) := by
  refine (injective_iff_map_eq_one _).2 fun q hq => ?_
  induction q using QuotientGroup.induction_on with | H w => ?_
  rw [inclFreeVarsHom_mk, QuotientGroup.eq_one_iff, inclFreeVars_mem_Rad_addFreeVars] at hq
  exact (QuotientGroup.eq_one_iff w).2 hq

variable {ι} in
/-- Evaluation at a solution `v` of the system with free variables `Y` restricts, on the
coordinate group of the system, to evaluation at the restriction of `v` to `X`. -/
@[simp]
theorem evalGHom_inclFreeVarsHom {v : X ⊕ Y → H} (hv : v ∈ V ι (addFreeVars Y S))
    (q : CoordGroup ι S) :
    evalGHom v hv (inclFreeVarsHom ι Y S q) =
      evalGHom (v ∘ Sum.inl) (mem_V_addFreeVars.1 hv) q := by
  induction q using QuotientGroup.induction_on
  simp

variable {ι} in
@[simp]
theorem evalGHom_comp_inclFreeVarsHom {v : X ⊕ Y → H} (hv : v ∈ V ι (addFreeVars Y S)) :
    (evalGHom v hv).comp (inclFreeVarsHom ι Y S) =
      evalGHom (v ∘ Sum.inl) (mem_V_addFreeVars.1 hv) :=
  GHom.ext fun _ => by simp

variable {ι} in
/-- The embedding `G_{R(S)} → G_{R(S')}` is compatible, through `G_S → G_S ∗ F(Y) ≃ G_{S'}`, with
the projections `G_S → G_{R(S)}` and `G_{S'} → G_{R(S')}`. -/
@[simp]
theorem inclFreeVarsHom_toCoordGroup (q : SystemGroup G S) :
    inclFreeVarsHom ι Y S (SystemGroup.toCoordGroup ι S q) =
      SystemGroup.toCoordGroup ι (addFreeVars Y S)
        ((SystemGroup.addFreeVarsEquiv Y S).symm (inl q)) := by
  induction q using QuotientGroup.induction_on
  simp

/-- The `G`-homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` from the free product of the coordinate
group of a system `S` with the free group on `Y` to the coordinate group of `S` with free
variables `Y`. -/
def freeVarsHom (Y : Type*) (S : Set (GX G X)) :
    GHom ((inl : CoordGroup ι S →* GX (CoordGroup ι S) Y).comp (coeff ι S))
      (coeff ι (addFreeVars Y S)) where
  toMonoidHom := eval (inclFreeVarsHom ι Y S : CoordGroup ι S →* CoordGroup ι (addFreeVars Y S))
    fun y => ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S))
  map_coeff' g := by simp

variable {ι} in
@[simp]
theorem freeVarsHom_inl (q : CoordGroup ι S) :
    freeVarsHom ι Y S (inl q) = inclFreeVarsHom ι Y S q := by
  simp [freeVarsHom]

variable {ι} in
private theorem freeVarsHom_toQuotientFreeVars (t : GX G (X ⊕ Y)) :
    freeVarsHom ι Y S (toQuotientFreeVars Y (Rad ι S) t) =
      (t : CoordGroup ι (addFreeVars Y S)) := by
  have h : (freeVarsHom ι Y S : _ →* _).comp (toQuotientFreeVars Y (Rad ι S)) =
      QuotientGroup.mk' (Rad ι (addFreeVars Y S)) :=
    hom_ext (MonoidHom.ext fun _ => by simp [toQuotientFreeVars])
      (FreeGroup.ext_hom _ _ fun x => by cases x <;> simp [toQuotientFreeVars, freeVarsHom])
  exact DFunLike.congr_fun h t

variable {ι} in
@[simp]
theorem freeVarsHom_inr (w : FreeGroup Y) :
    freeVarsHom ι Y S (inr w) =
      ((inr (FreeGroup.map Sum.inr w) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) := by
  rw [← toQuotientFreeVars_inr_map (Rad ι S) w, freeVarsHom_toQuotientFreeVars]

variable {ι} in
theorem freeVarsHom_inr_of (y : Y) :
    freeVarsHom ι Y S (inr (FreeGroup.of y)) =
      ((inr (FreeGroup.of (Sum.inr y)) : GX G (X ⊕ Y)) : CoordGroup ι (addFreeVars Y S)) := by
  simp

/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is surjective. -/
theorem freeVarsHom_surjective (Y : Type*) (S : Set (GX G X)) :
    Function.Surjective (freeVarsHom ι Y S) := fun q => by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨_, freeVarsHom_toQuotientFreeVars t⟩

variable {ι} in
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

variable {ι} in
/-- The homomorphism `G_{R(S)} ∗ F(Y) → G_{R(S')}` is compatible, through `G_S ∗ F(Y) ≃ G_{S'}`,
with the projections `G_S → G_{R(S)}` and `G_{S'} → G_{R(S')}`. -/
@[simp]
theorem freeVarsHom_map_toCoordGroup (w : GX (SystemGroup G S) Y) :
    freeVarsHom ι Y S
        (Monoid.Coprod.map (SystemGroup.toCoordGroup ι S : SystemGroup G S →* CoordGroup ι S)
          (.id _) w) =
      SystemGroup.toCoordGroup ι (addFreeVars Y S)
        ((SystemGroup.addFreeVarsEquiv Y S).symm w) := by
  induction w using induction_on with
  | inl q => simp
  | inr w => simp
  | mul x y hx hy => simp [hx, hy]

variable {ι} in
/-- The kernel of `G_{R(S)} ∗ F(Y) → G_{R(S')}` consists of the elements killed by every
homomorphism `G_{R(S)} ∗ F(Y) → H` given by a solution of `S` in `H` and values of `Y` in `H`. -/
theorem freeVarsHom_eq_one_iff {w : GX (CoordGroup ι S) Y} :
    freeVarsHom ι Y S w = 1 ↔
      ∀ (v : X → H) (hv : v ∈ V ι S) (u : Y → H),
        eval (evalGHom v hv : CoordGroup ι S →* H) u w = 1 := by
  obtain ⟨t, rfl⟩ := toQuotientFreeVars_surjective (Rad ι S) w
  have key (v : X → H) (hv : v ∈ V ι S) (u : Y → H) :
      eval (evalGHom v hv : CoordGroup ι S →* H) u (toQuotientFreeVars Y (Rad ι S) t) =
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
        eval (evalGHom v hv : CoordGroup ι S →* H) u w ≠ 1 := by
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
    have hφ : eval (ψ : CoordGroup ι S →* H) (fun y => φ (inr (FreeGroup.of y))) w = φ w :=
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
