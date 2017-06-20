module Rval where
--
import Types
import Expr
import Error
import Ctx
import Util
--
import Control.Monad.Except
import Control.Monad.Reader
--
-- type Check a = ExceptT ErrorMsg (Reader (Ctx VName a)) a
--
-- rval :: Expr -> Check Val
