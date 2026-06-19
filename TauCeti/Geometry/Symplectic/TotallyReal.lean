import Mathlib.LinearAlgebra.Projection

/-!
# Totally real linear subspaces

This file supplies the linear-algebra notion of a totally real subspace with respect to a
real-linear endomorphism `J`.  It is the pointwise model for totally real boundary conditions
in the analytic Heegaard Floer roadmap: a boundary tangent space `L` is totally real when
`L` and its `J`-image are complementary.

No integrability, topology, or symplectic form is bundled here.
-/

namespace TauCeti

open LinearMap

variable {R E F : Type*}
variable [Ring R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]

namespace LinearMap

/-- The standard complex structure on the doubled module `E × E`, sending `(x, y)` to
`(-y, x)`. -/
def standardComplexStructure (R E : Type*) [Ring R] [AddCommGroup E] [Module R E] :
    E × E →ₗ[R] E × E where
  toFun x := (-x.2, x.1)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' r x := by
    ext <;> simp

@[simp]
theorem standardComplexStructure_apply (x : E × E) :
    standardComplexStructure R E x = (-x.2, x.1) :=
  rfl

@[simp]
theorem standardComplexStructure_fst (x : E × E) :
    (standardComplexStructure R E x).1 = -x.2 :=
  rfl

@[simp]
theorem standardComplexStructure_snd (x : E × E) :
    (standardComplexStructure R E x).2 = x.1 :=
  rfl

@[simp]
theorem standardComplexStructure_comp_self :
    (standardComplexStructure R E).comp (standardComplexStructure R E) = -LinearMap.id :=
  LinearMap.ext fun x => by
    ext <;> simp

end LinearMap

/-- A submodule is totally real with respect to `J` if it is complementary to its `J`-image. -/
def IsTotallyReal (J : E →ₗ[R] E) (L : Submodule R E) : Prop :=
  IsCompl L (L.map J)

namespace IsTotallyReal

variable {J : E →ₗ[R] E} {K : F →ₗ[R] F} {L L' : Submodule R E} {M : Submodule R F}

theorem isCompl (hL : IsTotallyReal J L) : IsCompl L (L.map J) :=
  hL

theorem disjoint (hL : IsTotallyReal J L) : Disjoint L (L.map J) :=
  hL.isCompl.disjoint

theorem inf_eq_bot (hL : IsTotallyReal J L) : L ⊓ L.map J = ⊥ :=
  hL.isCompl.inf_eq_bot

theorem codisjoint (hL : IsTotallyReal J L) : Codisjoint L (L.map J) :=
  hL.isCompl.codisjoint

theorem sup_eq_top (hL : IsTotallyReal J L) : L ⊔ L.map J = ⊤ :=
  hL.isCompl.sup_eq_top

theorem existsUnique_add (hL : IsTotallyReal J L) (x : E) :
    ∃! y : L × L.map J, (y.1 : E) + y.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod hL.isCompl x

/-- If `J² = -1`, applying `J` twice sends every submodule back to itself. -/
theorem map_map_eq_of_comp_self_eq_neg_id (L : Submodule R E)
    (hJ : J.comp J = -LinearMap.id) : (L.map J).map J = L := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hxy : J (J z) = -z := by
      simpa using congr_fun (show ⇑(J.comp J) = ⇑(-LinearMap.id : E →ₗ[R] E) by
        rw [hJ]) z
    rw [hxy]
    exact L.neg_mem hz
  · intro hx
    refine ⟨J (-x), ?_, ?_⟩
    · exact ⟨-x, L.neg_mem hx, rfl⟩
    · have hxx : J (J (-x)) = -(-x) := by
        simpa using congr_fun (show ⇑(J.comp J) = ⇑(-LinearMap.id : E →ₗ[R] E) by
          rw [hJ]) (-x)
      simpa using hxx

theorem image (hL : IsTotallyReal J L) (hJ : J.comp J = -LinearMap.id) :
    IsTotallyReal J (L.map J) := by
  dsimp [IsTotallyReal]
  rw [map_map_eq_of_comp_self_eq_neg_id (J := J) L hJ]
  exact hL.isCompl.symm

theorem image_iff (hJ : J.comp J = -LinearMap.id) :
    IsTotallyReal J (L.map J) ↔ IsTotallyReal J L := by
  constructor
  · intro h
    have h' := h.image hJ
    rwa [map_map_eq_of_comp_self_eq_neg_id (J := J) L hJ] at h'
  · intro h
    exact h.image hJ

theorem prod (hL : IsTotallyReal J L) (hM : IsTotallyReal K M) :
    IsTotallyReal (LinearMap.prodMap J K) (L.prod M) := by
  dsimp [IsTotallyReal]
  rw [LinearMap.prodMap_map_prod]
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, hL.inf_eq_bot, hM.inf_eq_bot, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, hL.sup_eq_top, hM.sup_eq_top, Submodule.prod_top]

end IsTotallyReal

namespace Submodule

/-- The first factor in `E × E` is totally real for the standard complex structure. -/
theorem isTotallyReal_prod_top_bot_standardComplexStructure :
    IsTotallyReal (LinearMap.standardComplexStructure R E)
      ((⊤ : Submodule R E).prod (⊥ : Submodule R E)) := by
  dsimp [IsTotallyReal]
  have hmap :
      ((⊤ : Submodule R E).prod (⊥ : Submodule R E)).map
          (LinearMap.standardComplexStructure R E) =
        (⊥ : Submodule R E).prod (⊤ : Submodule R E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simpa using hy.2, trivial⟩
    · intro hx
      have hx1 : x.1 = 0 := by
        simpa using hx.1
      refine ⟨(x.2, 0), by simp, ?_⟩
      ext <;> simp [hx1]
  rw [hmap]
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, inf_bot_eq, bot_inf_eq, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, top_sup_eq, bot_sup_eq, Submodule.prod_top]

/-- The second factor in `E × E` is totally real for the standard complex structure. -/
theorem isTotallyReal_prod_bot_top_standardComplexStructure :
    IsTotallyReal (LinearMap.standardComplexStructure R E)
      ((⊥ : Submodule R E).prod (⊤ : Submodule R E)) := by
  dsimp [IsTotallyReal]
  have hmap :
      ((⊥ : Submodule R E).prod (⊤ : Submodule R E)).map
          (LinearMap.standardComplexStructure R E) =
        (⊤ : Submodule R E).prod (⊥ : Submodule R E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨trivial, by simpa using hy.1⟩
    · intro hx
      have hx2 : x.2 = 0 := by
        simpa using hx.2
      refine ⟨(0, -x.1), by simp, ?_⟩
      ext <;> simp [hx2]
  rw [hmap]
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, bot_inf_eq, top_inf_eq, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, bot_sup_eq, top_sup_eq, Submodule.prod_top]

end Submodule

end TauCeti
