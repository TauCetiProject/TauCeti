import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection

/-!
# Totally real linear subspaces

This file supplies the linear-algebra notion of a totally real subspace with respect to a
linear endomorphism `J` over an arbitrary scalar semiring.  This is the algebraic pointwise
model for totally real boundary conditions in the analytic Heegaard Floer roadmap: a boundary
tangent space `L` is totally real when `L` and its `J`-image are complementary.  The name is
borrowed from the usual real-linear situation, but the complement API itself is purely
module-theoretic.

No integrability, topology, or symplectic form is bundled here.
-/

namespace TauCeti

open LinearMap

variable {R E F : Type*}

section Basic

variable [Semiring R]
variable [AddCommMonoid E] [Module R E]
variable [AddCommMonoid F] [Module R F]

/-- A submodule is totally real with respect to `J` if it is complementary to its `J`-image. -/
def IsTotallyReal (J : E →ₗ[R] E) (L : Submodule R E) : Prop :=
  IsCompl L (L.map J)

@[simp]
theorem isTotallyReal_iff (J : E →ₗ[R] E) (L : Submodule R E) :
    IsTotallyReal J L ↔ IsCompl L (L.map J) :=
  Iff.rfl

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

/-- Products of totally real submodules are totally real for `LinearMap.prodMap`. -/
theorem prod (hL : IsTotallyReal J L) (hM : IsTotallyReal K M) :
    IsTotallyReal (LinearMap.prodMap J K) (L.prod M) := by
  rw [isTotallyReal_iff]
  rw [LinearMap.prodMap_map_prod]
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, hL.inf_eq_bot, hM.inf_eq_bot, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, hL.sup_eq_top, hM.sup_eq_top, Submodule.prod_top]

end IsTotallyReal

end Basic

section AddCommGroup

variable [Semiring R]
variable [AddCommGroup E] [Module R E]

namespace Submodule

/-- The image of the first coordinate factor under the standard doubled-module complex
structure is the second coordinate factor. -/
@[simp]
theorem map_prod_top_bot_skewSwap :
    ((⊤ : Submodule R E).prod (⊥ : Submodule R E)).map
        (LinearEquiv.skewSwap R E E).toLinearMap =
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

/-- The image of the second coordinate factor under the standard doubled-module complex
structure is the first coordinate factor. -/
@[simp]
theorem map_prod_bot_top_skewSwap :
    ((⊥ : Submodule R E).prod (⊤ : Submodule R E)).map
        (LinearEquiv.skewSwap R E E).toLinearMap =
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

/-- The first factor in `E × E` is totally real for the standard doubled-module complex
structure. -/
theorem isTotallyReal_prod_top_bot_skewSwap :
    IsTotallyReal (LinearEquiv.skewSwap R E E).toLinearMap
      ((⊤ : Submodule R E).prod (⊥ : Submodule R E)) := by
  rw [isTotallyReal_iff]
  rw [map_prod_top_bot_skewSwap]
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, inf_bot_eq, bot_inf_eq, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, top_sup_eq, bot_sup_eq, Submodule.prod_top]

/-- The second factor in `E × E` is totally real for the standard doubled-module complex
structure. -/
theorem isTotallyReal_prod_bot_top_skewSwap :
    IsTotallyReal (LinearEquiv.skewSwap R E E).toLinearMap
      ((⊥ : Submodule R E).prod (⊤ : Submodule R E)) := by
  rw [isTotallyReal_iff]
  rw [map_prod_bot_top_skewSwap]
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, bot_inf_eq, inf_bot_eq, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, bot_sup_eq, top_sup_eq, Submodule.prod_top]

end Submodule

end AddCommGroup

section Ring

variable [Ring R]
variable [AddCommGroup E] [Module R E]

namespace IsTotallyReal

variable {J : E →ₗ[R] E} {L : Submodule R E}

/-- If `J² = -1`, the image `J(L)` is totally real whenever `L` is totally real. -/
theorem image (hL : IsTotallyReal J L) (hJ : J.comp J = -LinearMap.id) :
    IsTotallyReal J (L.map J) := by
  rw [isTotallyReal_iff, ← Submodule.map_comp J J L, hJ, Submodule.map_neg, Submodule.map_id]
  exact hL.isCompl.symm

/-- Under `J² = -1`, `L` is totally real if and only if its image `J(L)` is totally real. -/
theorem image_iff (hJ : J.comp J = -LinearMap.id) :
    IsTotallyReal J (L.map J) ↔ IsTotallyReal J L := by
  constructor
  · intro h
    have h' := h.image hJ
    rwa [← Submodule.map_comp J J L, hJ, Submodule.map_neg, Submodule.map_id] at h'
  · intro h
    exact h.image hJ

end IsTotallyReal

namespace IsTotallyReal

variable {J : E →ₗ[R] E} {L : Submodule R E}

/-- Every vector decomposes uniquely as an element of `L` plus an element of `J(L)`. -/
theorem existsUnique_add (hL : IsTotallyReal J L) (x : E) :
    ∃! y : L × L.map J, (y.1 : E) + y.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod hL.isCompl x

end IsTotallyReal

end Ring

end TauCeti
